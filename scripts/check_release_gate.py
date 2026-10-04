#!/usr/bin/env python3
"""Fail-closed release gate: recorded R01-R14 plus current source/hash binding.

This validates the packaged acceptance evidence. It is not an independent
re-execution of the mathematical tests; CI labels its fresh core replay separately.
"""
import argparse
import hashlib
import json
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
a = p.parse_args()
root = a.root.resolve()
gate = json.loads((root/'verification/release_gate.json').read_text())
if gate.get('status') != 'PASS':
    raise SystemExit('FAIL: top-level release gate is not PASS')
expected = {f'R{i:02d}' for i in range(1, 15)}
gates = gate.get('gates')
if not isinstance(gates, dict) or set(gates) != expected:
    raise SystemExit('FAIL: exactly R01-R14 are required')
def check_digest(relative, digest):
    path = (root/relative).resolve()
    if not path.is_relative_to(root) or not path.is_file():
        raise SystemExit(f'FAIL: invalid or absent bound file {relative}')
    if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        raise SystemExit(f'FAIL: hash mismatch {relative}')

for name in sorted(expected):
    if gates[name].get('status') != 'PASS':
        raise SystemExit(f'FAIL: {name} is not semantically PASS')
    receipts = gates[name].get('receipts')
    if not isinstance(receipts, list) or not receipts:
        raise SystemExit(f'FAIL: {name} has no bound receipt evidence')
    for receipt in receipts:
        if not isinstance(receipt, dict) or not {'path','sha256'} <= set(receipt):
            raise SystemExit(f'FAIL: malformed {name} receipt reference')
        check_digest(receipt['path'], receipt['sha256'])
binding = gate.get('source_binding')
if not isinstance(binding, dict) or not binding:
    raise SystemExit('FAIL: nonempty source_binding is required')
required = {
    'artifact_v0.1.1/'+name for name in (
        'SOS14.json','EXACT_KERNELS.json','EXACT_SOS_CANDIDATE.json','POSITIVITY_CERTIFICATE.json',
        'verify_sos14.py','verify_independent.py','verify_statement.py','validate_integer_encoding.py',
        'strict_schema.py','verification_receipt.py','kill_tests.py','PROOF.md','ROOT_EMBEDDING.md','POVM_BRIDGE.md','SCHEMA.md')
} | {'paper/main.tex','paper/references.bib','paper/main.pdf','paper/README.md'}
# Generated input tables and their checker are load-bearing paper sources too.
required |= {str(p.relative_to(root)) for p in (root/'paper').glob('*') if p.is_file() and p.suffix in {'.tex','.bib','.py'}}
missing = required-set(binding)
if missing:
    raise SystemExit('FAIL: required source binding absent: '+', '.join(sorted(missing)))
for relative, digest in binding.items():
    check_digest(relative, digest)
for needed in ('paper/main.tex','paper/references.bib','paper/main.pdf','paper/README.md'):
    if not (root/needed).is_file():
        raise SystemExit(f'FAIL: missing manuscript deliverable {needed}')
print(f'PASS: all R01-R14 semantic gates and {len(binding)} bound source files; manuscript files present')
