#!/usr/bin/env python3
"""Install a hash-pinned Lean runtime and exact public dependencies for CI replay.

No credentials, Lake updates, fork caches, or project proof objects are accepted.
The caller installs the hash-pinned Python requirement first.
"""
import sys
sys.dont_write_bytecode = True
if sys.flags.optimize != 0:
    raise SystemExit('Optimized Python execution is forbidden for verification and setup')
import argparse, hashlib, json, os, platform, re, subprocess, tarfile, urllib.request
from pathlib import Path
from lean_replay_paths import validate_checkout_paths
ROOT = Path(__file__).resolve().parents[1]

def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def validate_pins(root, pins):
    manifest = root / 'lean/lake-manifest.json'
    if sha(manifest) != pins['lake_manifest_sha256']:
        raise RuntimeError('Lake manifest differs from pinned bytes')
    data = json.loads(manifest.read_text())
    if data.get('packagesDir') != '.lake/packages':
        raise RuntimeError('Unexpected dependency directory')
    if (root / 'lean/lean-toolchain').read_text().strip() != 'leanprover/lean4:v' + pins['lean_version']:
        raise RuntimeError('Lean toolchain differs from pinned version')
    for dep in data['packages']:
        if (dep.get('type') != 'git' or dep.get('subDir') is not None or
            not re.fullmatch(r'[A-Za-z0-9_-]+', dep['name']) or
            not re.fullmatch(r'https://github.com/[A-Za-z0-9_-]+/[A-Za-z0-9_.-]+', dep['url']) or
            not re.fullmatch(r'[0-9a-f]{40}', dep['rev'])):
            raise RuntimeError('Unsupported dependency descriptor: ' + repr(dep))
    mathlib = [d for d in data['packages'] if d['name'] == 'mathlib']
    if len(mathlib) != 1 or mathlib[0]['rev'] != pins['mathlib_revision']:
        raise RuntimeError('Unexpected mathlib revision')
    return data

def direct_mathlib_imports(root):
    modules = set()
    for source in [root / 'lean/CGLMP5.lean', *sorted((root / 'lean/CGLMP5').rglob('*.lean'))]:
        for line in source.read_text().splitlines():
            if line.startswith('import '):
                modules.update(x for x in line[7:].split() if x.startswith('Mathlib.'))
                if 'Mathlib' in line[7:].split():
                    raise RuntimeError('Broad Mathlib import would download an unbounded cache')
    if not modules:
        raise RuntimeError('No mathlib imports discovered')
    return sorted(modules)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work-dir', type=Path, required=True)
    args = parser.parse_args()
    validate_checkout_paths(ROOT)
    work = args.work_dir.resolve()
    if work.is_relative_to(ROOT):
        raise SystemExit('Runtime and setup receipts must be outside the repository')
    work.mkdir(parents=True, exist_ok=True)
    pins = json.loads((ROOT / 'verification/lean/ci/pins.json').read_text())
    data = validate_pins(ROOT, pins)
    if sys.version_info[:2] != (3, 12) or platform.system() != 'Linux' or platform.machine() != 'x86_64':
        raise SystemExit('Pinned CI bootstrap requires CPython 3.12 on Linux x86_64')
    import zstandard
    archive = work / Path(pins['lean_archive_url']).name
    if not archive.exists():
        temporary = archive.with_suffix(archive.suffix + '.download')
        with urllib.request.urlopen(pins['lean_archive_url'], timeout=120) as response, temporary.open('wb') as target:
            while block := response.read(1024 * 1024):
                target.write(block)
        temporary.replace(archive)
    if sha(archive) != pins['lean_archive_sha256']:
        raise RuntimeError('Lean archive SHA256 mismatch')
    runtime = work / pins['lean_archive_root']
    if not runtime.exists():
        with archive.open('rb') as source, zstandard.ZstdDecompressor().stream_reader(source) as stream, tarfile.open(fileobj=stream, mode='r|') as tar:
            for entry in tar:
                if not Path(entry.name).parts or Path(entry.name).parts[0] != pins['lean_archive_root']:
                    raise RuntimeError('Unexpected archive root: ' + entry.name)
                tar.extract(entry, path=work, filter='data')
    env = os.environ.copy()
    env.pop('PYTHONOPTIMIZE', None)
    env['PATH'] = str(runtime / 'bin') + os.pathsep + env['PATH']
    env['LEAN_NUM_THREADS'] = '1'
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    for key in ('LEAN_SYSROOT', 'LEAN_PATH', 'LEAN_SRC_PATH'):
        env.pop(key, None)
    prefix = subprocess.check_output([str(runtime / 'bin/lean'), '--print-prefix'], env=env, text=True).strip()
    if Path(prefix).resolve() != runtime:
        raise RuntimeError('Lean resolves an unexpected runtime prefix')
    # Do not allow caller cache overrides to widen cache provenance.
    for key in list(env):
        if key.startswith('MATHLIB_CACHE_'):
            del env[key]
    logs = []
    def run(name, command, cwd=ROOT):
        log = work / (name + '.log')
        with log.open('w') as out:
            result = subprocess.run(command, cwd=cwd, env=env, stdout=out, stderr=subprocess.STDOUT)
        logs.append({'name': name, 'command': command, 'exit': result.returncode, 'log': str(log)})
        if result.returncode:
            raise RuntimeError('Setup failed; see ' + str(log))
    run('runtime_readback', [sys.executable, str(ROOT / 'scripts/check_lean_runtime.py'), '--archive', str(archive), '--runtime', str(runtime), '--output', str(work / 'RUNTIME.json')])
    packages = ROOT / 'lean/.lake/packages'
    packages.mkdir(parents=True, exist_ok=True)
    for dep in data['packages']:
        target = packages / dep['name']
        if not target.exists():
            target.mkdir()
            run(dep['name'] + '_init', ['git', 'init', str(target)])
            run(dep['name'] + '_remote', ['git', 'remote', 'add', 'origin', dep['url']], target)
            run(dep['name'] + '_fetch', ['git', 'fetch', '--depth=1', 'origin', dep['rev']], target)
            run(dep['name'] + '_checkout', ['git', 'checkout', '--detach', dep['rev']], target)
        actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=target, text=True).strip()
        dirty = subprocess.check_output(['git', 'status', '--porcelain'], cwd=target, text=True).strip()
        if actual != dep['rev'] or dirty:
            raise RuntimeError('Dependency not clean at pinned revision: ' + dep['name'])
    imports = direct_mathlib_imports(ROOT)
    run('mathlib_cache', ['lake', 'exe', 'cache', 'get', '--cache-from=master,legacy', *imports], ROOT / 'lean')
    validate_pins(ROOT, pins)
    (work / 'SETUP.json').write_text(json.dumps({'status': 'PASS', 'pins': pins, 'runtime': str(runtime), 'archive': str(archive), 'platform': platform.platform(), 'python': sys.version, 'mathlib_imports': imports, 'dependencies': data['packages'], 'commands': logs}, indent=2) + '\n')
    if os.environ.get('GITHUB_PATH'):
        with open(os.environ['GITHUB_PATH'], 'a') as f:
            f.write(str(runtime / 'bin') + '\n')
    print('Pinned runtime ready: ' + str(runtime / 'bin'))

if __name__ == '__main__':
    main()
