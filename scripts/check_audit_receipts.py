#!/usr/bin/env python3
"""Check audit-receipt consistency, never infer scientific correctness from JSON.

The candidate repository is read-only. All reports and outputs must be external.
"""
import sys
sys.dont_write_bytecode = True
import argparse, datetime, hashlib, json, re
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[1]
UTC = datetime.timezone.utc
TREE = re.compile(r'[0-9a-f]{40}')
SHA = re.compile(r'[0-9a-f]{64}')
STAMP = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d{1,6})?(?:Z|\+00:00)')

def sha256(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def unique_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate JSON key: ' + key)
        result[key] = value
    return result

def has_symlink(path):
    return any(p.is_symlink() for p in (path, *path.parents))

def inside(path, root):
    return path == root or root in path.parents

class Validation:
    def __init__(self, base, tree, now):
        self.base, self.tree, self.now = base, tree, now
        self.errors, self.artifacts = [], {}
        self.report_paths = set()
        self.referenced_paths = set()
    def fail(self, where, message):
        self.errors.append(where + ': ' + message)
    def fields(self, obj, required, where):
        if not isinstance(obj, dict):
            self.fail(where, 'expected an object')
            return False
        missing, extra = set(required) - set(obj), set(obj) - set(required)
        if missing: self.fail(where, 'missing fields: ' + ', '.join(sorted(missing)))
        if extra: self.fail(where, 'unknown fields: ' + ', '.join(sorted(extra)))
        return not missing and not extra
    def text(self, value, where):
        if not isinstance(value, str) or not value.strip():
            self.fail(where, 'expected nonempty text')
            return False
        return True
    def timestamp(self, value, where):
        if not isinstance(value, str) or not STAMP.fullmatch(value):
            self.fail(where, 'expected explicit UTC timestamp')
            return None
        try:
            t = datetime.datetime.fromisoformat(value.replace('Z', '+00:00'))
            if t.tzinfo is None or t.utcoffset() != datetime.timedelta(0):
                raise ValueError('not explicit UTC')
            return t.astimezone(UTC)
        except ValueError:
            self.fail(where, 'invalid or non-UTC timestamp')
            return None
    def interval(self, obj, where, enclosing=None):
        start = self.timestamp(obj['started_utc'], where + '.started_utc')
        end = self.timestamp(obj['finished_utc'], where + '.finished_utc')
        if start is not None and end is not None:
            if not start < end: self.fail(where, 'start must precede finish')
            if end > self.now: self.fail(where, 'finish is in the future')
            if enclosing and (start < enclosing[0] or end > enclosing[1]):
                self.fail(where, 'worker interval is outside its round')
            return start, end
        return None
    def artifact(self, obj, where, report=False):
        if not self.fields(obj, ['path', 'sha256'], where): return
        name, expected = obj['path'], obj['sha256']
        if not isinstance(name, str) or not name or '\\' in name:
            self.fail(where, 'artifact path must be a nonempty portable relative path')
            return
        rel = PurePosixPath(name)
        if rel.is_absolute() or any(p in ('', '.', '..') for p in name.split('/')):
            self.fail(where, 'artifact path traversal or absolute path is forbidden')
            return
        path = self.base.joinpath(*rel.parts)
        self.referenced_paths.add(name)
        if has_symlink(path) or not inside(path.resolve(), self.base) or inside(path.resolve(), ROOT):
            self.fail(where, 'artifact symlink or bundle escape is forbidden')
            return
        if not isinstance(expected, str) or not SHA.fullmatch(expected):
            self.fail(where, 'expected lowercase SHA256')
            return
        if not path.is_file():
            self.fail(where, 'artifact is missing or not a regular file')
            return
        try:
            actual = sha256(path)
        except OSError as error:
            self.fail(where, 'artifact is unreadable: ' + str(error))
            return
        if actual != expected: self.fail(where, 'artifact SHA256 mismatch')
        previous = self.artifacts.get(name)
        if previous and previous['sha256'] != expected:
            self.fail(where, 'conflicting digests for one artifact')
        self.artifacts[name] = {'sha256': actual, 'bytes': path.stat().st_size}
        if report:
            if name in self.report_paths: self.fail(where, 'report reused for multiple coverage records')
            self.report_paths.add(name)
    def artifact_list(self, value, where, minimum=0):
        if not isinstance(value, list):
            self.fail(where, 'expected an artifact list')
            return
        if len(value) < minimum: self.fail(where, 'at least one evidence artifact is required')
        for i, item in enumerate(value): self.artifact(item, f'{where}[{i}]')
    def findings(self, value, where):
        if not isinstance(value, list):
            self.fail(where, 'expected an explicit findings list')
            return
        ids = set()
        for i, finding in enumerate(value):
            loc = f'{where}[{i}]'
            if not self.fields(finding, ['id', 'actionable', 'resolved', 'resolution', 'evidence'], loc):
                continue
            ident = finding['id']
            if self.text(ident, loc + '.id'):
                if ident in ids: self.fail(loc, 'duplicate finding id in one list')
                ids.add(ident)
            if type(finding['actionable']) is not bool or type(finding['resolved']) is not bool:
                self.fail(loc, 'actionable/resolved must be booleans')
            if finding['actionable'] is True and finding['resolved'] is not True:
                self.fail(loc, 'unresolved actionable finding')
            if not isinstance(finding['resolution'], str):
                self.fail(loc, 'resolution must be text, possibly empty only for nonactionable observations')
            if finding['actionable'] is True:
                self.text(finding['resolution'], loc + '.resolution')
            self.artifact_list(finding['evidence'], loc + '.evidence',
                               minimum=1 if finding['actionable'] is True else 0)
    def worker(self, obj, where, enclosing):
        keys = ['worker_id', 'coverage', 'status', 'started_utc', 'finished_utc',
                'report', 'attacks', 'findings']
        if not self.fields(obj, keys, where): return None
        ident = obj['worker_id']
        if not self.text(ident, where + '.worker_id'): ident = None
        self.text(obj['coverage'], where + '.coverage')
        if obj['status'] != 'PASS': self.fail(where, 'worker status must explicitly be PASS')
        self.interval(obj, where, enclosing)
        self.artifact(obj['report'], where + '.report', report=True)
        self.artifact_list(obj['attacks'], where + '.attacks', minimum=1)
        self.findings(obj['findings'], where + '.findings')
        return ident
    def fresh_route(self, obj, where, enclosing):
        keys = ['status', 'initial_attacks_finished_utc', 'started_utc', 'finished_utc',
                'report', 'attacks', 'findings']
        if not self.fields(obj, keys, where): return
        if obj['status'] != 'PASS': self.fail(where, 'fresh-route status must explicitly be PASS')
        interval = self.interval(obj, where, enclosing)
        initial = self.timestamp(obj['initial_attacks_finished_utc'], where + '.initial_attacks_finished_utc')
        if initial is not None and interval is not None:
            if initial > interval[0]: self.fail(where, 'fresh route starts before initial attacks finish')
            if enclosing and initial <= enclosing[0]: self.fail(where, 'initial attacks must occur within round3 before fresh routes')
        old_paths = set(self.artifacts)
        old_hashes = {a['sha256'] for a in self.artifacts.values()}
        self.artifact(obj['report'], where + '.report', report=True)
        self.artifact_list(obj['attacks'], where + '.attacks', minimum=1)
        refs = [obj['report']] + (obj['attacks'] if isinstance(obj['attacks'], list) else [])
        seen_paths, seen_hashes = set(), set()
        for ref in refs:
            if not isinstance(ref, dict): continue
            name, digest = ref.get('path'), ref.get('sha256')
            if isinstance(name, str) and isinstance(digest, str):
                if name in old_paths or digest in old_hashes or name in seen_paths or digest in seen_hashes:
                    self.fail(where, 'fresh-route evidence must not reuse earlier paths or identical bytes')
                seen_paths.add(name); seen_hashes.add(digest)
        self.findings(obj['findings'], where + '.findings')
    def round(self, obj, number, previous):
        where = f'rounds[{number-1}]'
        keys = ['round', 'status', 'git_tree', 'started_utc', 'finished_utc',
                'report', 'workers', 'findings']
        if number == 3: keys.append('fresh_route_pass')
        if not self.fields(obj, keys, where): return None
        if type(obj['round']) is not int or obj['round'] != number:
            self.fail(where, 'rounds must occur exactly in order 1,2,3')
        if obj['status'] != 'PASS': self.fail(where, 'round status must explicitly be PASS')
        if obj['git_tree'] != self.tree: self.fail(where, 'Git tree differs from supplied tree')
        interval = self.interval(obj, where)
        if interval and previous and interval[0] < previous[1]:
            self.fail(where, 'round overlaps or precedes the previous round')
        self.artifact(obj['report'], where + '.report', report=True)
        workers = obj['workers']
        if not isinstance(workers, list) or len(workers) != 5:
            self.fail(where, 'exactly five worker coverage records are required')
        if isinstance(workers, list):
            ids = [self.worker(w, f'{where}.workers[{i}]', interval) for i, w in enumerate(workers)]
            valid = [x for x in ids if x is not None]
            if len(set(valid)) != len(valid): self.fail(where, 'duplicate worker identity')
        self.findings(obj['findings'], where + '.findings')
        if number == 3: self.fresh_route(obj['fresh_route_pass'], where + '.fresh_route_pass', interval)
        return interval

def validate_receipts(index, tree, now=None):
    index = Path(index)
    result = {'status': 'INCONSISTENT', 'scientific_pass_inferred': False,
              'scope': 'Structural/time/tree/evidence consistency only. Reports and scientific findings require independent review.',
              'supplied_git_tree': tree, 'errors': []}
    if not isinstance(tree, str) or not TREE.fullmatch(tree):
        result['errors'].append('Expected a lowercase 40-hex Git tree identity')
        return result
    if has_symlink(index) or not index.is_file():
        result['errors'].append('Index is missing, non-regular or symlinked')
        return result
    index = index.resolve()
    result['index_sha256'] = sha256(index)
    try:
        data = json.loads(index.read_text(), object_pairs_hook=unique_keys)
    except (ValueError, UnicodeError, OSError) as error:
        result['errors'].append('Invalid index JSON: ' + str(error))
        return result
    v = Validation(index.parent, tree, now or datetime.datetime.now(UTC))
    if v.fields(data, ['format_version', 'git_tree', 'rounds'], 'index'):
        if type(data['format_version']) is not int or data['format_version'] != 1:
            v.fail('index', 'unsupported format_version')
        if data['git_tree'] != tree: v.fail('index', 'Git tree differs from supplied tree')
        rounds = data['rounds']
        if not isinstance(rounds, list) or len(rounds) != 3:
            v.fail('index', 'exactly three rounds are required')
        if isinstance(rounds, list):
            previous = None
            for i, record in enumerate(rounds, 1):
                previous = v.round(record, i, previous)
    # Rehash after validation to catch evidence/index changes during the check.
    for name, expected in v.artifacts.items():
        path = index.parent / name
        if has_symlink(path) or not path.is_file() or sha256(path) != expected['sha256']:
            v.fail(name, 'artifact changed during validation')
    if sha256(index) != result['index_sha256']: v.fail('index', 'index changed during validation')
    result.update(errors=v.errors, verified_artifacts=v.artifacts,
                  referenced_artifact_paths=sorted(v.referenced_paths),
                  checked_utc=datetime.datetime.now(UTC).isoformat())
    result['status'] = 'CONSISTENT' if not v.errors else 'INCONSISTENT'
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tree', required=True)
    parser.add_argument('--receipts', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    index, output = args.receipts.resolve(), args.output.resolve()
    if inside(index, ROOT) or inside(output, ROOT):
        parser.error('Audit receipts and output must be outside the candidate repository')
    if has_symlink(args.receipts) or has_symlink(args.output):
        parser.error('Symlinked input/output paths are forbidden')
    if output.exists(): parser.error('Output already exists; preserve it and choose a fresh path')
    result = validate_receipts(args.receipts, args.tree)
    artifacts = {index.parent / p for p in result.get('referenced_artifact_paths', [])}
    if output == index or output in artifacts:
        parser.error('Output must not overwrite input evidence')
    output.parent.mkdir(parents=True, exist_ok=True)
    result['checker_sha256'] = sha256(Path(__file__))
    with output.open('x') as f: json.dump(result, f, indent=2); f.write('\n')
    print(json.dumps({'status': result['status'], 'scientific_pass_inferred': False,
                      'errors': result['errors']}, indent=2))
    return 0 if result['status'] == 'CONSISTENT' else 1

if __name__ == '__main__':
    raise SystemExit(main())
