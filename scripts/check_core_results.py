#!/usr/bin/env python3
"""Require semantic PASS from each fresh core checker, not only process success."""
import json
import sys
from pathlib import Path
root = Path(sys.argv[1])
for name in ('validate_integer_encoding', 'verify_sos14', 'verify_independent', 'verify_statement'):
    data = json.loads((root / (name + '.json')).read_text())
    if data.get('status') != 'PASS':
        raise SystemExit(f'{name}: semantic status is not PASS: {data.get("status")!r}')
print('PASS: all four core checker receipts explicitly report PASS')
