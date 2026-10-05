#!/usr/bin/env python3
"""Replay lightweight fiber leaves sequentially, with fair tickets and external receipts.

The proof source is unchanged. Each ticket checks at most eight leaves and yields
between leaves after approximately seventeen seconds. A running compiler is never
terminated merely to meet the batch budget. All output must be outside the source
repository, so replay does not mutate the frozen candidate.
"""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

SELF = Path(__file__).resolve()
ROOT = SELF.parents[1]


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--start', type=int, required=True, help='First fiber, inclusive (0–272)')
    parser.add_argument('--end', type=int, default=272, help='Last fiber, inclusive (default: 272)')
    parser.add_argument('--lake', default='lake', help='Lake executable path or command on PATH')
    parser.add_argument('--output-dir', type=Path, required=True, help='Receipt directory outside the repository')
    parser.add_argument('--batch', action='store_true', help=argparse.SUPPRESS)
    parser.add_argument('--validate-only', action='store_true', help='Check configuration without invoking any compiler')
    args = parser.parse_args()
    if not 0 <= args.start <= args.end <= 272:
        parser.error('Require 0 <= --start <= --end <= 272.')
    args.output_dir = args.output_dir.expanduser().resolve()
    if args.output_dir.is_relative_to(ROOT):
        parser.error('--output-dir must be outside the repository, including through symlinks.')
    if args.output_dir.exists() and not args.output_dir.is_dir():
        parser.error('--output-dir is not a directory.')
    executable = os.path.expanduser(args.lake)
    if os.sep in executable or (os.altsep and os.altsep in executable):
        executable = str(Path(executable).resolve())
    else:
        executable = shutil.which(executable)
    if not executable or not Path(executable).is_file() or not os.access(executable, os.X_OK):
        parser.error('--lake must identify an executable, directly or on PATH.')
    args.lake = executable
    return args


def run_batch(args, env):
    begun = time.monotonic()
    results = []
    next_index = args.start
    status = 0
    for index in range(args.start, min(args.start + 8, args.end + 1)):
        if results and time.monotonic() - begun >= 17:
            break
        name = f'SOSIndexFiber{index:03}'
        source = ROOT / 'lean/CGLMP5' / f'{name}.lean'
        log = args.output_dir / f'{name}.log'
        started = datetime.now(timezone.utc).isoformat()
        start_time = time.monotonic()
        with log.open('w') as stream:
            result = subprocess.run(
                [args.lake, 'build', 'CGLMP5.' + name], cwd=ROOT / 'lean', env=env,
                stdout=stream, stderr=subprocess.STDOUT)
        item = {
            'module': 'CGLMP5.' + name,
            'started_utc': started,
            'elapsed_seconds': time.monotonic() - start_time,
            'exit_code': result.returncode,
            'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
            'log_relative_to_output_dir': log.name,
        }
        (args.output_dir / f'{name}.receipt.json').write_text(json.dumps(item, indent=2) + '\n')
        results.append(item)
        print(name, 'PASS' if result.returncode == 0 else 'FAIL', flush=True)
        if result.returncode:
            status = result.returncode
            break
        next_index = index + 1
    receipt = {
        'next': next_index, 'exit_code': status,
        'elapsed_seconds': time.monotonic() - begun, 'results': results,
    }
    (args.output_dir / f'fiber_batch_{args.start:03}.json').write_text(json.dumps(receipt, indent=2) + '\n')
    return status


def main():
    args = parse_args()
    if args.validate_only:
        print(json.dumps({
            'start': args.start, 'end': args.end, 'lake': args.lake,
            'output_dir': str(args.output_dir), 'batch': args.batch,
            'compiler_invoked': False,
        }, sort_keys=True))
        return 0
    args.output_dir.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    if args.batch:
        return run_batch(args, env)
    index = args.start
    while index <= args.end:
        result = subprocess.run([
            sys.executable, str(ROOT / 'scripts/limited_build.py'), sys.executable, str(SELF),
            '--batch', '--start', str(index), '--end', str(args.end),
            '--lake', args.lake, '--output-dir', str(args.output_dir),
        ], cwd=ROOT / 'lean', env=env)
        if result.returncode:
            return result.returncode
        receipt = json.loads((args.output_dir / f'fiber_batch_{index:03}.json').read_text())
        if not index < receipt['next'] <= args.end + 1:
            raise RuntimeError('Batch receipt did not advance within the requested range.')
        index = receipt['next']
    print('All requested fiber leaves checked.', flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
