#!/usr/bin/env python3
"""Strict sequential Lean completion-gate replay. This does not replace the three audits."""
import sys
sys.dont_write_bytecode = True
if sys.flags.optimize != 0:
    raise SystemExit('Optimized Python execution is forbidden for verification and setup')
import argparse, json, os, platform, shutil, subprocess, time
from pathlib import Path
from negative_control_support import ReplayGuard
from lean_replay_paths import validate_checkout_paths
ROOT = Path(__file__).resolve().parents[1]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--runtime', type=Path, required=True)
    args = parser.parse_args()
    args.require_clean_tree = True
    paths = validate_checkout_paths(ROOT)
    guard = ReplayGuard(ROOT, args, args.output_dir)
    out = guard.out
    runtime = args.runtime.resolve()
    lake = runtime / 'bin/lake'
    for name in ('lean', 'lake'):
        found = shutil.which(name)
        if not found or Path(found).resolve() != (runtime / 'bin' / name).resolve():
            raise SystemExit('PATH must select the hash-pinned runtime: ' + name)
    env = os.environ.copy()
    env.pop('PYTHONOPTIMIZE', None)
    env.update(LEAN_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
    for key in ('LEAN_SYSROOT', 'LEAN_PATH', 'LEAN_SRC_PATH'):
        env.pop(key, None)
    prefix = subprocess.check_output([str(runtime / 'bin/lean'), '--print-prefix'], env=env, text=True).strip()
    if Path(prefix).resolve() != runtime:
        raise SystemExit('Lean resolves an unexpected runtime prefix')
    py = sys.executable
    lock = [py, str(ROOT / 'scripts/limited_build.py')]
    stages = [
        ('readiness', [py, 'scripts/check_lean_completion_readiness.py', '--output', str(out / 'READINESS.json')], ROOT),
        ('source_manifest', [py, 'scripts/check_source_manifest.py'], ROOT),
        ('mapped_inventory', [py, 'verification/lean/check_mapped_inventory.py', '--output', str(out / 'MAPPED_INVENTORY.json')], ROOT),
        ('mapped_inventory_guard_tests', [py, 'verification/lean/test_mapped_inventory.py'], ROOT),
        ('mapped_inventory_optimized_guard_tests', [py, '-O', 'verification/lean/test_mapped_inventory.py'], ROOT),
        ('axiom_report_guard_tests', [py, 'verification/lean/test_axiom_report.py'], ROOT),
        ('axiom_report_optimized_guard_tests', [py, '-O', 'verification/lean/test_axiom_report.py'], ROOT),
        ('runtime', [py, 'scripts/check_lean_runtime.py', '--archive', str(args.archive.resolve()), '--runtime', str(runtime), '--output', str(out / 'RUNTIME.json')], ROOT),
        ('inventory_guard_tests', [py, 'verification/lean/test_inspection_inventory.py'], ROOT),
        ('immutability_guard_tests', [py, 'scripts/test_negative_control_support.py'], ROOT),
        ('semantic_rejection_guard_tests', [py, 'scripts/test_lean_rejection.py'], ROOT),
        ('semantic_rejection_optimized_guard_tests', [py, '-O', 'scripts/test_lean_rejection.py'], ROOT),
        ('ci_guard_tests', [py, 'verification/lean/ci/test_ci_configuration.py'], ROOT),
        ('source_readback_guard_tests', [py, 'scripts/test_source_readback.py'], ROOT),
        ('source_manifest_guard_tests', [py, 'scripts/test_source_manifest.py'], ROOT),
        ('integrated_ci_guard_tests', [py, 'scripts/test_integrated_ci.py'], ROOT),
        ('audit_receipt_guard_tests', [py, 'scripts/test_audit_receipts.py'], ROOT),
        ('audit_receipt_optimized_guard_tests', [py, '-O', 'scripts/test_audit_receipts.py'], ROOT),
        ('path_containment_guard_tests', [py, 'scripts/test_lean_replay_paths.py'], ROOT),
        ('kernel_replay_pipeline_tests', [py, 'verification/lean/test_kernel_replay_pipeline.py'], ROOT),
        ('checker_fixture_classifier_tests', [py, 'verification/lean/test_checker_fixture_classifier.py'], ROOT),
        ('checker_fixture_classifier_optimized_tests', [py, '-O', 'verification/lean/test_checker_fixture_classifier.py'], ROOT),
        ('sos_corruption_classifier_tests', [py, 'verification/lean/test_sos_corruption_classifier.py'], ROOT),
        ('sos_corruption_classifier_optimized_tests', [py, '-O', 'verification/lean/test_sos_corruption_classifier.py'], ROOT),
        ('source_generator_reproducibility', [py, 'scripts/generate_lean_sos_source.py', '--check'], ROOT),
        ('arithmetic_generator_reproducibility', [py, 'scripts/generate_lean_sos_arithmetic.py', '--check'], ROOT),
        ('residual_generator_reproducibility', [py, 'scripts/generate_lean_sos_residual_stages.py', '--check'], ROOT),
        ('clean_build', lock + [py, str(ROOT / 'scripts/build_lean_clean.py'), '--receipt-dir', str(out / 'build'), '--clean-project', '--require-clean-git'], ROOT),
        ('frozen_inputs', [py, 'scripts/check_lean_frozen_inputs.py', '--output', str(out / 'FROZEN_INPUTS.json')], ROOT),
        ('source_chunks', [py, 'scripts/check_source_chunks.py', '--output', str(out / 'SOURCE_CHUNKS.json')], ROOT),
        ('actual_source_bytes', lock + [py, str(ROOT / 'scripts/check_lean_source_bytes.py'), '--output', str(out / 'SOURCE_BYTES.json')], ROOT),
        ('trust_surface', [py, 'scripts/check_lean_trust_surface.py', '--output', str(out / 'TRUST_SURFACE.json')], ROOT),
        ('types_axioms', lock + [py, str(ROOT / 'verification/lean/inspect_dependencies.py'), '--fail-if-pending', '--output', str(out / 'inspection')], ROOT / 'lean'),
        ('axiom_report_comparison', [py, 'verification/lean/check_axiom_report.py', '--inspection', str(out / 'inspection/inspection.json'), '--output', str(out / 'AXIOM_REPORT_COMPARISON.json')], ROOT),
        ('kernel_checker_control', lock + [py, str(ROOT / 'scripts/run_lean_checker_fixture.py'), '--lake', str(lake), '--output-dir', str(out / 'checker_control'), '--require-clean-tree'], ROOT),
        ('fresh_kernel_replay', lock + [py, str(ROOT / 'scripts/recheck_lean_kernel.py'), '--output-dir', str(out / 'kernel_replay'), '--runtime', str(runtime)], ROOT),
        ('negative_fixtures', lock + [py, str(ROOT / 'scripts/run_lean_negative_controls.py'), '--lake', str(lake), '--output-dir', str(out / 'negative_fixtures'), '--require-clean-tree'], ROOT),
        # This runner acquires its own slot per compiler. Do not wrap it again.
        ('source_mutations', [py, 'scripts/run_lean_source_mutations.py', '--lake', str(lake), '--output-dir', str(out / 'source_mutations'), '--require-clean-tree'], ROOT),
        ('source_decode_corruption', lock + [py, str(ROOT / 'scripts/run_lean_source_binding_corruption.py'), '--lake', str(lake), '--output-dir', str(out / 'source_decode_corruption'), '--require-clean-tree'], ROOT),
        ('actual_sos_corruption', lock + [py, str(ROOT / 'scripts/run_lean_sos_corruption.py'), '--lake', str(lake), '--output-dir', str(out / 'actual_sos_corruption'), '--require-clean-tree'], ROOT),
    ]
    receipt = {'status': 'RUNNING', 'platform': platform.platform(), 'python': sys.version, 'head': guard.baseline['head'], 'tree': guard.baseline['tree'],
               'path_validation': paths, 'scope': 'Completion-gate replay only; three same-tree adversarial audit rounds are separately required.', 'stages': []}
    def save():
        (out / 'VERIFICATION_RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
    save()
    try:
        for name, command, cwd in stages:
            guard.check(name + ':before')
            started = time.monotonic()
            logfile = out / (name + '.log')
            print('Running ' + name, flush=True)
            with logfile.open('w') as log:
                result = subprocess.run(command, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT)
            receipt['stages'].append({'name': name, 'command': command, 'exit': result.returncode,
                                      'seconds': time.monotonic() - started, 'log': str(logfile)})
            save()
            guard.check(name + ':after')
            if result.returncode:
                raise RuntimeError(name + ' failed; see ' + str(logfile))
        guard.check('complete')
        receipt['status'] = 'PASS'
    except BaseException as exc:
        receipt['status'] = 'FAIL'
        receipt['error'] = str(exc)
        save()
        raise
    save()
    print('Completion-gate replay PASS: ' + str(out / 'VERIFICATION_RECEIPT.json'))

if __name__ == '__main__':
    main()
