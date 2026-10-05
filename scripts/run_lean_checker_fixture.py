#!/usr/bin/env python3
"""Validate the official checker against a controlled external invalid proof object.

This is a negative-control fixture, never a production proof or import. The outer
caller owns the heavyweight slot. Only the temporary shadow contains compiled
fixture objects. Source/type/axiom inspection is not substituted for kernel replay.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import argparse, datetime, hashlib, json, os, signal, subprocess, tempfile, time
from negative_control_support import ReplayGuard, add_replay_arguments

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'verification/lean_negative_controls/checker_fixture'
NAMES = ('ValidObject', 'InvalidObject', 'ImportValid', 'ImportInvalid')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def is_kernel_mismatch(log, returncode, timed_out):
    bad = ('failed to import', 'unknown module', 'unknown constant', 'no such file',
           'out of memory', 'maximum recursion', 'maximum number of heartbeats',
           'stack overflow', 'segmentation fault', 'interrupted', 'timeout')
    return (returncode == 1 and not timed_out
            and "while replaying declaration 'TrustFixture.claim'" in log
            and '(kernel) declaration type mismatch' in log
            and 'True' in log and 'False' in log
            and not any(s in log.lower() for s in bad))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', required=True)
    parser.add_argument('--timeout-seconds', type=int, default=900,
                        help='Per-process wall-clock bound; a timeout fails the control.')
    add_replay_arguments(parser)
    args = parser.parse_args()
    if args.timeout_seconds <= 0:
        parser.error('--timeout-seconds must be positive')
    if args.output_dir is None:
        parser.error('--output-dir is required for deliberate invalid-object fixtures')
    destination = args.output_dir.resolve()
    if destination == ROOT or ROOT in destination.parents:
        parser.error('Deliberate invalid-object fixture outputs must be outside the repository')
    guard = ReplayGuard(ROOT, args, ROOT / 'verification/lean_negative_controls/checker_runs')
    out = guard.out
    lake = Path(args.lake).resolve()
    lean = lake.with_name('lean')
    checker = lake.with_name('leanchecker')
    if not lean.is_file() or not checker.is_file():
        raise RuntimeError('Expected pinned official lean and leanchecker beside lake')
    runtime = subprocess.check_output([str(lean), '--version'], text=True).strip()
    search = subprocess.check_output([str(lake), 'env', 'printenv', 'LEAN_PATH'],
                                     cwd=ROOT / 'lean', text=True).strip()
    search = ':'.join(str((ROOT / 'lean' / p).resolve()) if not Path(p).is_absolute()
                      else p for p in search.split(':'))
    rows = []
    receipt = dict(status='RUNNING', kind='controlled_valid_invalid_object_kernel_replay',
                   scope='External negative-control fixtures only; never production imports.',
                   runner_sha256=sha(Path(__file__)), runtime_version=runtime,
                   binary_sha256={str(p): sha(p) for p in (lake, lean, checker)},
                   fixture_source_sha256={n: sha(FIXTURES / (n + '.lean')) for n in NAMES},
                   timeout_seconds=args.timeout_seconds, commands=rows)
    def save():
        receipt['frozen_replay'] = guard.metadata()
        (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    save()
    with tempfile.TemporaryDirectory(prefix='cglmp-checker-fixture-') as directory:
        temp = Path(directory)
        for name in NAMES:
            text = (FIXTURES / (name + '.lean')).read_text()
            (temp / (name + '.lean')).write_text(text)
            (out / (name + '.lean.txt')).write_text(text)
        env = os.environ.copy()
        env.update(LEAN_PATH=str(temp) + ':' + search, LEAN_NUM_THREADS='1')
        env['PATH'] = str(lake.parent) + os.pathsep + env.get('PATH', '')
        def run(label, command, expected, mismatch=False):
            guard.check(label + ':before')
            started = time.monotonic()
            process = subprocess.Popen(command, cwd=temp, env=env, text=True,
                                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            timed_out = False
            try:
                log = process.communicate(timeout=args.timeout_seconds)[0]
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    log = process.communicate(timeout=5)[0]
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    log = process.communicate()[0]
            (out / (label + '.log')).write_text(log)
            guard.check(label + ':after')
            passed = (is_kernel_mismatch(log, process.returncode, timed_out) if mismatch
                      else process.returncode == expected and not timed_out)
            rows.append(dict(label=label, command=command, exit=process.returncode,
                             timeout=timed_out, expected_exit=expected, passed=passed,
                             expected_kernel_mismatch=mismatch,
                             seconds=time.monotonic() - started,
                             log_sha256=hashlib.sha256(log.encode()).hexdigest()))
            save()
            print(label, process.returncode, 'passed', passed, flush=True)
            if not passed:
                receipt['status'] = 'FAIL'
                save()
                raise SystemExit(1)
        for name in ('ValidObject', 'InvalidObject'):
            run('compile_' + name, [str(lean), '-R', str(temp), '-o',
                str(temp / (name + '.olean')), str(temp / (name + '.lean'))], 0)
        receipt['fixture_object_sha256'] = {
            n: sha(temp / (n + '.olean')) for n in ('ValidObject', 'InvalidObject')}
        for name in ('Valid', 'Invalid'):
            run('import_trust0_' + name, [str(lean), '--trust=0', '-DmaxRecDepth=200000',
                '-DmaxHeartbeats=0', str(temp / ('Import' + name + '.lean'))], 0)
        for fresh in (False, True):
            for name, expected in (('ValidObject', 0), ('InvalidObject', 1)):
                label = ('checker_fresh_' if fresh else 'checker_module_') + name
                command = [str(checker)] + (['--fresh'] if fresh else []) + ['-v', name]
                run(label, command, expected, mismatch=(expected == 1))
        # Retain the deliberate object fixture as evidence, outside the candidate tree.
        for name in ('ValidObject', 'InvalidObject'):
            (out / (name + '.olean.fixture')).write_bytes((temp / (name + '.olean')).read_bytes())
    guard.check('complete')
    receipt.update(status='PASS', genuine_fresh_kernel_replay_validated=True,
                   trust_zero_import_does_not_validate_objects=True,
                   valid_fresh_replay_passes=True, invalid_fresh_replay_rejected_by_kernel=True,
                   completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    save()
    print('Receipt:', out / 'receipt.json')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
