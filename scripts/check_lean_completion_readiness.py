#!/usr/bin/env python3
"""Fail-closed readiness check; not proof validation or an adversarial audit."""
import sys
sys.dont_write_bytecode = True
import argparse, hashlib, importlib.util, json, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]

def check(root=ROOT):
    inspection = root / 'verification/lean/inspect_dependencies.py'
    spec = importlib.util.spec_from_file_location('cglmp_inspection', inspection)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    inventory = root / 'verification/lean/declaration_inventory.json'
    hooks = root / 'verification/lean/ci/completion_hooks.json'
    entries = json.loads(inventory.read_text()).get('declarations', [])
    errors = []
    if not entries:
        errors.append('Missing or empty declaration inventory')
    roles = {d.get('role') for d in entries if d.get('status') == 'ready'}
    errors += ['Final root is not ready: ' + r for r in sorted(module.REQUIRED_FINAL_ROLES - roles)]
    errors += ['Pending declaration: ' + d.get('role', '?') for d in entries if d.get('status') != 'ready']
    names = {d.get('name') for d in entries if d.get('status') == 'ready'}
    errors += ['Required scalar declaration absent: ' + n for n in sorted(module.REQUIRED_SCALAR_DECLARATIONS - names)]
    for d in entries:
        if d.get('status') == 'ready':
            name, mod = d.get('name'), d.get('module')
            if not all(isinstance(x, str) and re.fullmatch(r'CGLMP5(?:\.[A-Za-z_][A-Za-z_0-9]*)+', x) for x in (name, mod)):
                errors.append('Invalid ready entry: ' + repr(d))
            elif not (root / 'lean' / Path(*mod.split('.')).with_suffix('.lean')).is_file():
                errors.append('Missing production module: ' + mod)
    hook = json.loads(hooks.read_text()).get('actual_sos_coefficient_corruption', {})
    expected = 'scripts/run_lean_sos_corruption.py'
    if hook.get('status') != 'ready' or hook.get('runner') != expected or not (root / expected).is_file():
        errors.append('Required actual SOS coefficient corruption hook is pending or missing')
    return {'status': 'READY' if not errors else 'BLOCKED', 'errors': errors,
            'scope': 'Readiness only; full proof, trust, source, and mutation gates still required.',
            'inventory_sha256': hashlib.sha256(inventory.read_bytes()).hexdigest(),
            'hooks_sha256': hashlib.sha256(hooks.read_bytes()).hexdigest()}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise SystemExit('Readiness receipt must be outside the repository')
    result = check()
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    return 0 if result['status'] == 'READY' else 1

if __name__ == '__main__':
    raise SystemExit(main())
