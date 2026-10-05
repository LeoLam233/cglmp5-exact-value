#!/usr/bin/env python3
"""Reject a validly encoded SOS Gram-coefficient mutation in the actual residual proof.

Both the numeric datum and its definitional lookup literal change together. Every
module on that local numeric dependency path is recompiled in a private shadow.
Rejection must occur in unchanged SOSIntegerResidual000 arithmetic, not lookup or
source-decoding proofs. The outer caller holds one heavyweight build slot.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import argparse, ast, hashlib, json, os, re, subprocess, tempfile, time
from negative_control_support import ReplayGuard, add_replay_arguments

ROOT = Path(__file__).resolve().parents[1]
CHAIN = ['SOSIntegerData', 'SOSIntegerResidualDefinitions', 'SOSIntegerLiterals',
         'SOSPhaseLinearData', 'SOSPhaseLinear00', 'SOSIntegerResidual000']

def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()

def classify_rejection(log, returncode):
    """Accept only the one intended arithmetic error, never infrastructure failure."""
    forbidden = [s for s in [
        'unknown identifier', 'unknown constant', 'unknown module', 'object file',
        'no such file', 'invalid header', 'failed to import', 'maximum recursion',
        'maximum number of heartbeats', 'out of memory', 'stack overflow',
        'segmentation fault', 'interrupted', 'timeout'
    ] if s in log.lower()]
    headers = [line for line in log.splitlines() if re.search(r':\d+:\d+: error:', line)]
    expected = (returncode == 1 and len(headers) == 1
                and 'SOSIntegerResidual000.lean:' in headers[0]
                and 'Tactic `decide` proved that the proposition' in headers[0]
                and sum(line.strip() == 'is false' for line in log.splitlines()) == 1
                and not forbidden)
    return dict(actual_arithmetic_false=expected, error_headers=headers,
                infrastructure_or_resource_diagnostics=forbidden)

def change_first_gram_coordinate(data, literals):
    datum = re.search(r'(def gramNumerator\b.*?\| 0 => !\[)(-?\d+)', data, re.S)
    lookup = re.search(r'(theorem gram_numerator_literal_0 : gramNumerator 0 = !\[)(-?\d+)', literals)
    if not datum or not lookup or datum[2] != lookup[2]:
        raise RuntimeError('Expected matching source datum and exact definitional lookup literal')
    old, new = datum[2], str(int(datum[2]) + 1)
    mutated_data = data[:datum.start(2)] + new + data[datum.end(2):]
    mutated_literals = literals[:lookup.start(2)] + new + literals[lookup.end(2):]
    fiber = re.search(r'theorem fiber_literal_0 : fiber 0 = (\[.*?\]) :=', literals)
    if not fiber:
        raise RuntimeError('Expected exact word-zero fiber literal')
    terms = ast.literal_eval(fiber[1])
    affected = [t for t in terms if t[0] == 0]
    if affected != [(0, 0)] * 8:
        raise RuntimeError('Unexpected support for the selected Gram coefficient')
    return mutated_data, mutated_literals, old, new

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', required=True)
    add_replay_arguments(parser)
    args = parser.parse_args()
    lean = ROOT / 'lean'
    guard = ReplayGuard(ROOT, args, ROOT / 'verification/lean_negative_controls/sos_runs')
    out = guard.out
    tool = str(Path(args.lake).with_name('lean'))
    basepath = subprocess.check_output([args.lake, 'env', 'printenv', 'LEAN_PATH'], cwd=lean, text=True).strip()
    basepath = ':'.join(str((lean / p).resolve()) if not Path(p).is_absolute() else p for p in basepath.split(':'))
    sources = {n: (lean / 'CGLMP5' / (n + '.lean')).read_text() for n in CHAIN}
    mutated_data, mutated_literals, old, new = change_first_gram_coordinate(sources['SOSIntegerData'], sources['SOSIntegerLiterals'])
    results = []
    receipt = dict(kind='actual_SOS_residual_coefficient_corruption_not_final_audit',
                   runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   expected_rejection_module='CGLMP5.SOSIntegerResidual000',
                   mutated_coordinate='gramNumerator 0 0', old_numerator=old, new_numerator=new,
                   affected_features={'word': 0, 'features': [[0, 0]] * 8},
                   source_sha256={n: digest(s) for n, s in sources.items()},
                   mutation_sha256={'SOSIntegerData': digest(mutated_data), 'SOSIntegerLiterals': digest(mutated_literals)},
                   lookup_literal_updated_to_match_mutant=True,
                   expected_failure_layer='integer residual arithmetic after valid data and lookup rebuilds',
                   dependency_chain=CHAIN, results=results, status='RUNNING')
    def save():
        receipt['frozen_replay'] = guard.metadata()
        (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    save()
    if args.require_clean_tree:
        # A frozen candidate must first have the actual identity, not just its finite layer.
        guard.check('identity_freshness:before')
        check = subprocess.run([args.lake, '--no-build', 'build', 'CGLMP5.SOSIdentity'], cwd=lean, text=True, capture_output=True)
        (out / 'identity_freshness.log').write_text(check.stdout + check.stderr)
        guard.check('identity_freshness:after')
        receipt['actual_identity_freshness_exit'] = check.returncode
        if check.returncode:
            receipt['status'] = 'FAIL_IDENTITY_NOT_CURRENT'
            save()
            raise SystemExit(1)
    for mode in ('original', 'mutated'):
        runs = []
        with tempfile.TemporaryDirectory(prefix='cglmp-sos-corruption-') as temp:
            temp = Path(temp)
            namespace = temp / 'CGLMP5'
            namespace.mkdir()
            # Lean searches a module namespace at the first matching root. Preserve the
            # whole immutable namespace while excluding every object being recompiled.
            for dep in (lean / '.lake/build/lib/lean/CGLMP5').iterdir():
                if dep.is_file() and dep.name.split('.')[0] not in CHAIN:
                    (namespace / dep.name).symlink_to(dep.resolve())
            env = os.environ.copy()
            env.update(LEAN_PATH=str(temp) + ':' + basepath, LEAN_NUM_THREADS='1')
            lastlog = ''
            for name in CHAIN:
                guard.check(mode + ':' + name + ':before')
                text = sources[name]
                if mode == 'mutated' and name == 'SOSIntegerData':
                    text = mutated_data
                elif mode == 'mutated' and name == 'SOSIntegerLiterals':
                    text = mutated_literals
                if name == 'SOSIntegerData':
                    # Fin24 typing fixes the numerator length; positive denominator
                    # certifies that this is still a valid exact rational encoding.
                    text += '\nnamespace CGLMP5.SOSFinite\nexample : 0 < gramDenominator 0 := all_denominators_positive.1 0\nend CGLMP5.SOSFinite\n'
                file = namespace / (name + '.lean')
                file.write_text(text)
                preserved = out / 'sources' / mode / (name + '.lean')
                preserved.parent.mkdir(parents=True, exist_ok=True)
                preserved.write_text(text)
                started = time.monotonic()
                process = subprocess.run([tool, '-R', str(temp), '-o', str(file.with_suffix('.olean')), str(file)], cwd=temp, env=env, text=True, capture_output=True)
                lastlog = process.stdout + process.stderr
                (out / (mode + '_' + name + '.log')).write_text(lastlog)
                guard.check(mode + ':' + name + ':after')
                runs.append(dict(module='CGLMP5.' + name, exit=process.returncode,
                                 compiled_source_sha256=digest(text),
                                 preserved_source=str(preserved.relative_to(out)),
                                 seconds=time.monotonic() - started))
                print(mode, name, process.returncode, flush=True)
                if process.returncode:
                    break
            earlier_passed = len(runs) == len(CHAIN) and all(r['exit'] == 0 for r in runs[:-1])
            classification = classify_rejection(lastlog, runs[-1]['exit'])
            passed = earlier_passed and (runs[-1]['exit'] == 0 if mode == 'original'
                                        else classification['actual_arithmetic_false'])
            results.append(dict(mode=mode, passed=passed, earlier_numeric_path_compiles=earlier_passed,
                                **classification, runs=runs))
            save()
        if not passed:
            break
    guard.check('complete')
    receipt['status'] = 'PASS' if len(results) == 2 and all(r['passed'] for r in results) else 'FAIL'
    save()
    print('Receipt: ' + str(out / 'receipt.json'))
    raise SystemExit(0 if receipt['status'] == 'PASS' else 1)

if __name__ == '__main__':
    main()
