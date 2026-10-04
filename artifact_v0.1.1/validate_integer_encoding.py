#!/usr/bin/env python3
"""Strict required-schema preflight; no identity or positivity certification."""
from pathlib import Path
import argparse
from strict_schema import FILES, check, integer, unique_object, require_normal_python
from verification_receipt import receipt, run_cli


def verify(root):
    require_normal_python();root=Path(root)
    rows=[check(root/n) for n in FILES]
    return {'status':'PASS','scope':'required exact-input schema only; no mathematical certification',
            'files':rows,'total_integer_scalars':sum(r['valid_integer_scalars'] for r in rows),
            'receipt':receipt('validate_integer_encoding.py',root,rows,['strict JSON and required schema for four certificate files only'])}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    return run_cli(lambda:verify(args.root),args.output)

if __name__=='__main__':
    raise SystemExit(main())
