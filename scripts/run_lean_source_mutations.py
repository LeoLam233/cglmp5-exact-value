#!/usr/bin/env python3
"""Isolated original/mutated production replay. This is not an adversarial audit round."""
import sys
sys.dont_write_bytecode = True
from negative_control_support import ReplayGuard, add_replay_arguments
from lean_rejection import BLOCKED_MARKERS, SOURCE_KINDS, classify_rejection
from pathlib import Path
import argparse, hashlib, json, os, subprocess, tempfile, time

CASES = [
    ('event_shift', 'Events.lean', 'a.val == (b.val + shift) % 5', 'a.val == (b.val + shift + 1) % 5'),
    ('same_party_order', 'WordSyntax.lean', 'else (a.1, k) :: w', 'else w ++ [(a.1, k)]'),
    ('root_embedding_sign', 'Root.lean', 'def mu : ℝ := Classical.choose exists_mu', 'def mu : ℝ := -(Classical.choose exists_mu)'),
    ('weight_sign', 'Positivity.lean', 'Scalar.evalReal (CanonicalData.weight j)', '-Scalar.evalReal (CanonicalData.weight j)'),
    ('setting_dependent_J', 'POVMDilation.lean', 'compression commonJ (E.dilate.effect a) = E.effect a', 'compression (defectUnitary E.analysis ∘L commonJ) (E.dilate.effect a) = E.effect a'),
]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--lake', required=True)
parser.add_argument('--timeout', type=int, default=1800)
parser.add_argument('--case', action='append', choices=[c[0] for c in CASES], help='Development-only selected controls; omitted for the complete suite.')
add_replay_arguments(parser)
args = parser.parse_args()
repo = Path(__file__).resolve().parents[1]
lean = repo / 'lean'
guard = ReplayGuard(repo, args, repo / 'verification/lean_negative_controls/source_runs')
out = guard.out
selected = [c for c in CASES if args.case is None or c[0] in args.case]
basepath = subprocess.check_output([args.lake, 'env', 'printenv', 'LEAN_PATH'], cwd=lean, text=True).strip()
basepath = ':'.join(str((lean / p).resolve()) if not Path(p).is_absolute() else p for p in basepath.split(':'))
tool = str(Path(args.lake).with_name('lean'))

def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()

def compile_one(label, command, cwd, env):
    guard.check(label + ':before')
    started = time.monotonic()
    try:
        process = subprocess.run([sys.executable, str(repo / 'scripts/limited_build.py'), *command], cwd=cwd, env=env, text=True, capture_output=True, timeout=args.timeout)
        code, log = process.returncode, process.stdout + process.stderr
    except subprocess.TimeoutExpired:
        code, log = None, 'TIMEOUT (including global slot wait)\n'
    (out / (label.replace(':', '_') + '.log')).write_text(log)
    guard.check(label + ':after')
    bad = any(s in log.lower() for s in BLOCKED_MARKERS)
    return dict(exit_code=code, timeout=code is None, unrelated_error=bad, seconds=round(time.monotonic() - started, 3)), log

results = []
for name, filename, old, new in selected:
    source = lean / 'CGLMP5' / filename
    original = source.read_text()
    if original.count(old) != 1:
        raise RuntimeError(f'{name}: expected one mutation anchor, found {original.count(old)}')
    mutated = original.replace(old, new)
    semantic = (lean / 'CGLMP5/Words.lean').read_text() if name == 'same_party_order' else None
    item = dict(name=name, source='CGLMP5/' + filename, original_sha256=sha(original), mutation_sha256=sha(mutated), old=old, new=new, runs=[])
    if semantic is not None:
        item['semantic_validator'] = 'CGLMP5/Words.lean'
        item['semantic_validator_sha256'] = sha(semantic)
    for mode, text in [('original', original), ('mutated', mutated)]:
        with tempfile.TemporaryDirectory(prefix='cglmp-source-mutation-') as temp:
            temp = Path(temp)
            env = os.environ.copy()
            env['LEAN_NUM_THREADS'] = '1'
            if semantic is not None:
                # Rebuild the genuine syntax module in a private first-priority namespace,
                # then check the unchanged production interpretation/evaluation proofs.
                (temp / 'CGLMP5').mkdir()
                syntax = temp / 'CGLMP5/WordSyntax.lean'
                syntax.write_text(text)
                env['LEAN_PATH'] = str(temp) + ':' + basepath
                syntax_result, syntax_log = compile_one(name + ':' + mode + ':syntax', [tool, '-R', str(temp), '-o', str(syntax.with_suffix('.olean')), str(syntax)], temp, env)
                if syntax_result['exit_code'] != 0:
                    item['runs'].append(dict(mode=mode, passed=False, syntax=syntax_result, reason='Syntax itself did not compile'))
                    break
                file = temp / 'CGLMP5/Words.lean'
                file.write_text(semantic)
                record, log = compile_one(name + ':' + mode + ':semantics', [tool, '-R', str(temp), str(file)], temp, env)
                record['syntax'] = syntax_result
            else:
                file = temp / filename
                file.write_text(text)
                record, log = compile_one(name + ':' + mode, [args.lake, 'env', 'lean', str(file)], lean, env)
            code = record['exit_code']
            diagnostic = None if mode == 'original' else classify_rejection(
                log, code, 'Words.lean' if semantic is not None else filename,
                SOURCE_KINDS[name], timed_out=record['timeout'])
            passed = code == 0 if mode == 'original' else diagnostic['accepted']
            item['runs'].append(dict(mode=mode, passed=passed, inspected_diagnostic=diagnostic, **record))
            print(name, mode, 'PASS' if passed else 'FAIL', code, flush=True)
        if not passed:
            break
    item['source_unchanged_during_case'] = source.read_text() == original
    item['passed'] = len(item['runs']) == 2 and all(r['passed'] for r in item['runs']) and item['source_unchanged_during_case']
    results.append(item)
    complete = len(results) == len(selected)
    receipt = dict(kind='production_source_mutation_controls_not_final_audit', results=results, complete_selected_cases=complete,
                   complete_suite=complete and len(selected) == len(CASES), selected_cases=[c[0] for c in selected],
                   frozen_replay=guard.metadata(), status='PASS' if complete and all(r['passed'] for r in results) else 'IN_PROGRESS_OR_FAIL')
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
guard.check('end')
print('Receipt:', out / 'receipt.json', flush=True)
raise SystemExit(0 if all(r['passed'] for r in results) else 1)
