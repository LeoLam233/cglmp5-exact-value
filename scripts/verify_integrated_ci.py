#!/usr/bin/env python3
"""Require the latest main-push run of each verification workflow at one commit.

This read-only receipt gate does not establish the external three-audit acceptance
record; the reviewed receipt hash must separately be supplied at release dispatch.
"""
import argparse
import json
from pathlib import Path
import re

REQUIRED = {'.github/workflows/verify.yml', '.github/workflows/lean-verification.yml'}


def verify(runs, commit):
    if not re.fullmatch('[0-9a-f]{40}', commit):
        raise ValueError('Expected a full lowercase commit SHA')
    accepted = []
    for path in sorted(REQUIRED):
        candidates = [r for r in runs if r.get('path') == path and r.get('head_sha') == commit
                      and r.get('head_branch') == 'main' and r.get('event') == 'push']
        if not candidates:
            raise ValueError('Missing integrated-main push CI: ' + path)
        latest = max(candidates, key=lambda r: (int(r['run_number']), int(r.get('run_attempt', 1))))
        if latest.get('status') != 'completed' or latest.get('conclusion') != 'success':
            raise ValueError('Latest integrated CI is not completed successfully: ' + path)
        accepted.append(latest)
    return {'status': 'PASS', 'integrated_commit': commit, 'required_workflows': sorted(REQUIRED),
            'runs': accepted, 'scope': 'Integrated-commit CI only; external same-tree acceptance is separate.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runs-jsonl', type=Path, required=True)
    parser.add_argument('--commit', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    runs = [json.loads(line) for line in args.runs_jsonl.read_text().splitlines() if line.strip()]
    result = verify(runs, args.commit)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
