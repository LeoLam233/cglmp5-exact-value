#!/usr/bin/env python3
"""Replay the complete final root using the official fresh-environment Lean checker.

Ordinary import with --trust=0 is not this replay. This stage must run alone after
fresh source compilation. It records exact object bytes before and after checking.
"""
import sys
sys.dont_write_bytecode = True
if sys.flags.optimize != 0:
    raise SystemExit('Optimized Python execution is forbidden for kernel replay')
import argparse, hashlib, json, os, platform, shutil, subprocess, time
from pathlib import Path
from negative_control_support import ReplayGuard
from lean_replay_paths import validate_checkout_paths
ROOT = Path(__file__).resolve().parents[1]

def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def object_snapshot(runtime):
    lean = ROOT / 'lean'
    manifest = json.loads((lean / 'lake-manifest.json').read_text())
    bases = [('runtime', runtime / 'lib/lean', True), ('project', lean / '.lake/build/lib/lean', True)]
    bases += [('dependency:' + p['name'], lean / '.lake/packages' / p['name'] / '.lake/build/lib/lean', False) for p in manifest['packages']]
    result = {}
    for label, base, required in bases:
        if not base.is_dir():
            if required:
                raise RuntimeError('Missing object directory: ' + str(base))
            result[label + '/@OBJECT_DIRECTORY_MISSING'] = None
            continue
        for path in sorted(base.rglob('*.olean*')):
            if path.is_file():
                result[label + '/' + path.relative_to(base).as_posix()] = sha(path)
    if not any(k == 'project/CGLMP5.olean' for k in result):
        raise RuntimeError('The final umbrella object is missing')
    return result

def replay_command(runtime):
    return [str(Path(runtime) / 'bin/lake'), 'env', 'leanchecker', '--fresh', 'CGLMP5']

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', required=True, type=Path)
    parser.add_argument('--runtime', required=True, type=Path)
    args = parser.parse_args()
    args.require_clean_tree = True
    validate_checkout_paths(ROOT)
    guard = ReplayGuard(ROOT, args, args.output_dir)
    out = guard.out
    runtime = args.runtime.resolve()
    lake, checker = runtime / 'bin/lake', runtime / 'bin/leanchecker'
    pins = json.loads((ROOT / 'verification/lean/ci/pins.json').read_text())
    if sha(checker) != pins['leanchecker_sha256']:
        raise RuntimeError('leanchecker differs from the pinned official archive')
    umbrella = (ROOT / 'lean/CGLMP5.lean').read_text()
    if not any(line.split() == ['import', 'CGLMP5.Main'] for line in umbrella.splitlines()):
        raise RuntimeError('The umbrella must import the complete CGLMP5.Main theorem module')
    env = os.environ.copy()
    for key in ('PYTHONOPTIMIZE', 'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT'):
        env.pop(key, None)
    env.update(LEAN_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
    env['PATH'] = str(runtime / 'bin') + os.pathsep + env['PATH']
    def output(command):
        return subprocess.check_output(command, cwd=ROOT / 'lean', env=env, text=True).strip()
    lake_path = output([str(lake), 'env', 'printenv', 'PATH'])
    located = shutil.which('leanchecker', path=lake_path)
    if not located or Path(located).resolve() != checker.resolve():
        raise RuntimeError('Lake would execute an unexpected checker')
    fresh = subprocess.run([str(lake), '--no-build', 'build', 'CGLMP5'], cwd=ROOT / 'lean', env=env, text=True, capture_output=True)
    (out / 'FRESHNESS.log').write_text(fresh.stdout + fresh.stderr)
    if fresh.returncode:
        raise RuntimeError('The final root is not a current source build')
    dependency_pins = json.loads((ROOT / 'lean/lake-manifest.json').read_text())['packages']
    dependency_receipts = []
    for dependency in dependency_pins:
        directory = ROOT / 'lean/.lake/packages' / dependency['name']
        actual = output(['git', '-C', str(directory), 'rev-parse', 'HEAD'])
        dirty = output(['git', '-C', str(directory), 'status', '--porcelain'])
        if actual != dependency['rev'] or dirty:
            raise RuntimeError('Dependency is not pinned and clean: ' + dependency['name'])
        dependency_receipts.append({'name': dependency['name'], 'revision': actual, 'url': dependency['url']})
    before = object_snapshot(runtime)
    (out / 'OBJECTS_BEFORE.json').write_text(json.dumps(before, indent=2) + '\n')
    command = replay_command(runtime)
    receipt = {'status': 'RUNNING', 'platform': platform.platform(),
               'uname': {k: v for k, v in platform.uname()._asdict().items() if k != 'node'},
               'python': sys.version, 'python_executable': sys.executable, 'dependencies': dependency_receipts,
               'lake_manifest_sha256': sha(ROOT / 'lean/lake-manifest.json'), 'method': 'replayFromFresh in official LeanChecker.lean, into an empty kernel environment',
               'command': command, 'head': guard.baseline['head'], 'tree': guard.baseline['tree'],
               'lean': output([str(runtime / 'bin/lean'), '--version']), 'lake': output([str(lake), '--version']),
               'leanchecker_sha256': sha(checker), 'object_files': sum(v is not None for v in before.values()),
               'objects_before_sha256': sha(out / 'OBJECTS_BEFORE.json'), 'module': 'CGLMP5',
               'scope': 'Complete imported-declaration kernel replay; separate from type/axiom inspection and adversarial audits.'}
    def save():
        (out / 'KERNEL_REPLAY_RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
    save()
    guard.check('kernel_replay:before')
    started = time.monotonic()
    with (out / 'LEANCHECKER.log').open('w') as log:
        result = subprocess.run(command, cwd=ROOT / 'lean', env=env, stdout=log, stderr=subprocess.STDOUT)
    receipt.update(exit_code=result.returncode, seconds=time.monotonic() - started)
    after = object_snapshot(runtime)
    (out / 'OBJECTS_AFTER.json').write_text(json.dumps(after, indent=2) + '\n')
    receipt.update(objects_after_sha256=sha(out / 'OBJECTS_AFTER.json'), objects_unchanged=before == after,
                   checker_unchanged=sha(checker) == pins['leanchecker_sha256'])
    try:
        guard.check('kernel_replay:after')
    except BaseException as error:
        receipt.update(status='FAIL', error=str(error))
        save()
        raise
    receipt['status'] = 'PASS' if result.returncode == 0 and before == after and receipt['checker_unchanged'] else 'FAIL'
    save()
    print(json.dumps({k: receipt[k] for k in ('status', 'exit_code', 'object_files', 'objects_unchanged', 'seconds')}))
    raise SystemExit(0 if receipt['status'] == 'PASS' else 1)

if __name__ == '__main__':
    main()
