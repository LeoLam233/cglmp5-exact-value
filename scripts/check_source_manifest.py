#!/usr/bin/env python3
"""Create or verify the complete repository file manifest before candidate freeze.

The manifest excludes only itself. Git supplies the candidate file set; ignored
build products and external audit receipts cannot enter it. This is byte-level
packaging evidence, never a mathematical proof or an audit-round PASS.
"""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = 'SOURCE_MANIFEST.sha256'


def candidate_files():
    raw = subprocess.check_output(
        ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'], cwd=ROOT)
    names = sorted(set(x.decode('utf-8') for x in raw.split(b'\0') if x))
    for name in names:
        if name == MANIFEST:
            continue
        path = Path(name)
        if path.is_absolute() or '..' in path.parts or '\n' in name or '\r' in name:
            raise RuntimeError('Unsupported manifest path: ' + repr(name))
        yield name


def render():
    lines = ['# Complete candidate repository byte manifest; paths relative to repository root.',
             '# Excludes only SOURCE_MANIFEST.sha256 itself; ignored build products are not source.',
             '# Audit/replay receipts produced after freezing are external, separately hashed assets.']
    for name in candidate_files():
        path = ROOT / name
        if path.is_symlink():
            data = os.readlink(path).encode('utf-8')
        elif path.is_file():
            data = path.read_bytes()
        else:
            raise RuntimeError('Tracked candidate file is absent or not regular: ' + name)
        lines.append(hashlib.sha256(data).hexdigest() + '  ' + name)
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='Regenerate before freezing the candidate tree')
    args = parser.parse_args()
    expected = render()
    path = ROOT / MANIFEST
    if args.write:
        path.write_text(expected)
        print('Wrote complete candidate byte manifest; this is not a proof or audit result.')
    elif path.read_text() != expected:
        raise SystemExit('FAIL: source manifest does not match the complete candidate file set and bytes')
    else:
        print('PASS: complete candidate source manifest matches every listed byte')


if __name__ == '__main__':
    main()
