#!/usr/bin/env python3
"""Check final release bytes against the validated proof payload, without replay.

The manifest partitions EVERY baseline tracked path into a frozen payload entry
or an explicit release-layer exclusion. Fixed allowlists prevent a manifest from
silently excluding new proof inputs. Public baseline 977800f and the validated
67e0426 commit have the same pinned Git tree; only the public object is needed.
This establishes byte identity, not a new build, audit, or scientific verdict.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASELINE_COMMIT = '977800fda115c7897655b068cf16e1c001778421'
VALIDATED_COMMIT = '67e0426166c622a63e7daae554560e1ece16a3ba'
BASELINE_TREE = 'c1a5aa737f6bd7f04ea2bc2c22424dd53bcea281'
MANIFEST = 'verification/final_payload_manifest.json'
RELEASE_EXCLUSIONS = frozenset({
    'README.md', 'FORMALIZATION_REPORT.md', 'RELEASE_v0.2.0.md',
    'AXIOM_AUDIT.md', 'STATEMENT_ALIGNMENT.md', 'RELEASE_NOTES.md',
    'SOURCE_MAP.md', 'docs/LEAN_REPLAY.md', 'docs/LEAN_SOS_SOURCE_MAP.md',
    'verification/lean_negative_controls/README.md', 'verification/lean/README.md',
    'SOURCE_MANIFEST.sha256',
    '.github/workflows/release-v0.2.0.yml',
    '.github/workflows/lean-verification.yml', 'scripts/verify_integrated_ci.py',
})
NEW_RELEASE_FILES = frozenset({
    MANIFEST, 'scripts/check_release_payload.py', 'scripts/test_release_payload.py',
})
FIELDS = frozenset({
    'format_version', 'baseline_commit', 'baseline_tree', 'validated_commit',
    'validated_tree', 'baseline_manifest_sha256', 'payload_sha256', 'files',
    'excluded_baseline_files',
})
ENTRY_FIELDS = frozenset({'path', 'mode', 'git_blob_sha1', 'bytes', 'sha256', 'role'})


def digest(data):
    return hashlib.sha256(data).hexdigest()


def unique_keys(pairs):
    obj = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError('Duplicate JSON key: ' + key)
        obj[key] = value
    return obj


def portable_path(value):
    return (isinstance(value, str) and bool(value)
            and not PurePosixPath(value).is_absolute() and '\\' not in value
            and all(ord(c) >= 32 and ord(c) != 127 for c in value)
            and not any(p in ('', '.', '..') for p in value.split('/')))


def git(root, *args):
    return subprocess.check_output(['git', *args], cwd=root, stderr=subprocess.PIPE)


def tree_entries(root, revision):
    result = {}
    for record in git(root, 'ls-tree', '-rz', '--full-tree', revision).split(b'\0'):
        if not record:
            continue
        meta, path = record.split(b'\t', 1)
        mode, kind, oid = meta.decode('ascii').split()
        result[path.decode('utf-8')] = (mode, kind, oid)
    return result


def baseline_hashes(root, entries):
    """Read pinned Git blobs in one process; never use working-tree substitutes."""
    result = {}
    with subprocess.Popen(['git', 'cat-file', '--batch'], cwd=root,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as process:
        try:
            for name, (_, kind, oid) in entries.items():
                if kind != 'blob':
                    raise ValueError('Non-blob baseline entry: ' + name)
                process.stdin.write((oid + '\n').encode('ascii'))
                process.stdin.flush()
                header = process.stdout.readline().decode('ascii').strip().split()
                if len(header) != 3 or header[:2] != [oid, 'blob']:
                    raise ValueError('Invalid Git blob response for ' + name)
                size = int(header[2])
                content = process.stdout.read(size)
                if len(content) != size or process.stdout.read(1) != b'\n':
                    raise ValueError('Truncated Git blob response for ' + name)
                result[name] = (size, digest(content))
        finally:
            process.stdin.close()
        if process.wait() != 0:
            raise ValueError('Git blob read failed')
    return result


def check(root=ROOT, manifest=None):
    root = Path(root).resolve()
    manifest = Path(manifest) if manifest else root / MANIFEST
    result = {'status': 'FAIL', 'scientific_pass_inferred': False,
              'scope': 'Byte identity only; no new proof replay or audit is inferred.',
              'errors': []}
    errors = result['errors']
    try:
        if manifest.is_symlink() or not manifest.is_file():
            raise ValueError('Manifest must be a regular non-symlink file')
        raw = manifest.read_bytes()
        data = json.loads(raw, object_pairs_hook=unique_keys)
        if not isinstance(data, dict) or set(data) != FIELDS:
            raise ValueError('Manifest fields do not match payload schema v1')
        if type(data['format_version']) is not int or data['format_version'] != 1:
            raise ValueError('Unsupported payload format_version')
        expected = dict(baseline_commit=BASELINE_COMMIT, baseline_tree=BASELINE_TREE,
                        validated_commit=VALIDATED_COMMIT, validated_tree=BASELINE_TREE)
        for key, value in expected.items():
            if data[key] != value:
                raise ValueError('Pinned provenance mismatch: ' + key)
        if git(root, 'rev-parse', '--show-toplevel').decode().strip() != str(root):
            raise ValueError('Root must be the Git checkout root')
        if git(root, 'rev-parse', BASELINE_COMMIT + '^{tree}').decode().strip() != BASELINE_TREE:
            raise ValueError('Public baseline tree differs from validated pinned tree')
        baseline = tree_entries(root, BASELINE_COMMIT)
        final = tree_entries(root, 'HEAD')
        index = {}
        for record in git(root, 'ls-files', '--stage', '-z').split(b'\0'):
            if not record:
                continue
            meta, name = record.split(b'\t', 1)
            mode, oid, stage = meta.decode('ascii').split()
            if stage != '0':
                raise ValueError('Unmerged index entry')
            index[name.decode('utf-8')] = (mode, 'blob', oid)
        others = {p.decode('utf-8') for p in git(root, 'ls-files', '--others',
                  '--exclude-standard', '-z').split(b'\0') if p}
        if not isinstance(data['files'], list) or not data['files']:
            raise ValueError('Nonempty payload files list is required')
        files = {}
        for entry in data['files']:
            if not isinstance(entry, dict) or set(entry) != ENTRY_FIELDS:
                raise ValueError('Malformed payload file entry')
            name = entry['path']
            if not portable_path(name) or name in files:
                raise ValueError('Invalid or duplicate payload path: ' + repr(name))
            if (entry['mode'] not in ('100644', '100755')
                    or not isinstance(entry['git_blob_sha1'], str)
                    or not re.fullmatch('[0-9a-f]{40}', entry['git_blob_sha1'])
                    or type(entry['bytes']) is not int or entry['bytes'] < 0
                    or not isinstance(entry['sha256'], str)
                    or not re.fullmatch('[0-9a-f]{64}', entry['sha256'])
                    or not isinstance(entry['role'], str) or not entry['role'].strip()):
                raise ValueError('Malformed payload metadata: ' + name)
            files[name] = entry
        if list(files) != sorted(files):
            raise ValueError('Payload files must be sorted by path')
        excluded = set()
        if not isinstance(data['excluded_baseline_files'], list):
            raise ValueError('Explicit baseline exclusions list is required')
        for entry in data['excluded_baseline_files']:
            if (not isinstance(entry, dict) or set(entry) != {'path', 'reason'}
                    or not portable_path(entry['path'])
                    or not isinstance(entry['reason'], str) or not entry['reason'].strip()):
                raise ValueError('Malformed release-layer exclusion')
            name = entry['path']
            if name not in RELEASE_EXCLUSIONS or name in excluded:
                raise ValueError('Unauthorized or duplicate release-layer exclusion: ' + name)
            excluded.add(name)
        if set(files) & excluded:
            raise ValueError('Payload and exclusions overlap')
        if set(files) | excluded != set(baseline):
            raise ValueError('Payload and exclusions must partition every baseline tracked path')
        unexpected = (set(final) | set(index) | others) - set(baseline) - NEW_RELEASE_FILES
        if unexpected:
            raise ValueError('Unapproved new release path: ' + ', '.join(sorted(unexpected)))
        missing = set(baseline) - (set(final) & set(index))
        if missing:
            raise ValueError('Baseline tracked paths removed: ' + ', '.join(sorted(missing)))
        hashes = baseline_hashes(root, baseline)
        if data['baseline_manifest_sha256'] != hashes['SOURCE_MANIFEST.sha256'][1]:
            raise ValueError('Historical SOURCE_MANIFEST baseline digest mismatch')
        lines = ''.join(files[name]['sha256'] + '  ' + name + '\n' for name in sorted(files))
        if data['payload_sha256'] != digest(lines.encode('utf-8')):
            raise ValueError('Payload aggregate SHA256 mismatch')
        for name, entry in files.items():
            identity = (entry['mode'], 'blob', entry['git_blob_sha1'])
            if baseline[name] != identity or hashes[name] != (entry['bytes'], entry['sha256']):
                errors.append('Manifest entry differs from baseline Git object: ' + name)
            if final.get(name) != identity:
                errors.append('Final HEAD payload differs from baseline: ' + name)
            if index.get(name) != identity:
                errors.append('Index payload differs from baseline: ' + name)
            path = root / name
            if (not path.is_file() or any(p.is_symlink() for p in (path, *path.parents))
                    or not path.resolve().is_relative_to(root)):
                errors.append('Missing, escaped, or symlinked payload file: ' + name)
                continue
            mode = '100755' if path.stat().st_mode & 0o111 else '100644'
            content = path.read_bytes()
            if mode != entry['mode'] or len(content) != entry['bytes'] or digest(content) != entry['sha256']:
                errors.append('Working-tree payload differs from baseline: ' + name)
        if manifest.read_bytes() != raw:
            errors.append('Manifest changed during verification')
        result.update(manifest_sha256=digest(raw), payload_sha256=data['payload_sha256'],
                      baseline_commit=BASELINE_COMMIT, baseline_tree=BASELINE_TREE,
                      validated_commit=VALIDATED_COMMIT, validated_tree=BASELINE_TREE,
                      final_commit=git(root, 'rev-parse', 'HEAD').decode().strip(),
                      final_tree=git(root, 'rev-parse', 'HEAD^{tree}').decode().strip(),
                      payload_file_count=len(files), excluded_baseline_paths=sorted(excluded))
    except (ValueError, OSError, UnicodeError, subprocess.CalledProcessError) as error:
        errors.append(str(error))
    result['status'] = 'PASS' if not errors else 'FAIL'
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    if output.is_relative_to(ROOT) or any(p.is_symlink() for p in (args.output, *args.output.parents)):
        parser.error('Output must be external to the checkout and not symlinked')
    if output.exists():
        parser.error('Output already exists; preserve it and choose a fresh path')
    result = check()
    result['checker_sha256'] = digest(Path(__file__).read_bytes())
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open('x') as handle:
        json.dump(result, handle, indent=2)
        handle.write('\n')
    print(json.dumps(result, indent=2))
    return 0 if result['status'] == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
