#!/usr/bin/env python3
"""Executable unit tests for external-output/frozen-tree guards; uses only a disposable toy repo."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from types import SimpleNamespace
import argparse,json,subprocess,tempfile
from negative_control_support import ReplayGuard
p=argparse.ArgumentParser();p.add_argument('--output-file',type=Path);a=p.parse_args();results=[]
with tempfile.TemporaryDirectory(prefix='cglmp-replay-guard-test-') as td:
    t=Path(td);r=t/'repo';r.mkdir()
    def git(*args):subprocess.run(['git','-C',str(r),*args],check=True,capture_output=True)
    git('init','-q');(r/'source').write_text('original\n');git('add','source')
    git('-c','user.name=Replay Test','-c','user.email=replay@example.invalid','commit','-qm','original')
    g=ReplayGuard(r,SimpleNamespace(output_dir=t/'receipts',require_clean_tree=True),t/'unused')
    g.check('clean');results.append(dict(test='clean_external_output',passed=g.metadata()['all_checkpoints_clean']))
    (r/'source').write_text('changed\n')
    try:g.check('changed_source');ok=False
    except RuntimeError:ok=(g.out/'IMMUTABILITY_FAILURE.json').exists()
    results.append(dict(test='detect_changed_source',passed=ok))
    try:ReplayGuard(r,SimpleNamespace(output_dir=t/'receipts2',require_clean_tree=True),t/'unused');ok=False
    except RuntimeError:ok=True
    results.append(dict(test='reject_dirty_start',passed=ok));git('restore','source')
    try:ReplayGuard(r,SimpleNamespace(output_dir=r/'receipts',require_clean_tree=True),t/'unused');ok=False
    except RuntimeError:ok=True
    results.append(dict(test='reject_in_tree_output',passed=ok))
    g2=ReplayGuard(r,SimpleNamespace(output_dir=t/'head_receipts',require_clean_tree=True),t/'unused')
    git('-c','user.name=Replay Test','-c','user.email=replay@example.invalid','commit','--allow-empty','-qm','changed_head')
    try:g2.check('changed_head');ok=False
    except RuntimeError:ok=True
    results.append(dict(test='detect_clean_head_change',passed=ok))
text=json.dumps(dict(status='PASS' if all(x['passed'] for x in results) else 'FAIL',tests=results),indent=2)+'\n'
print(text,end='')
if a.output_file:a.output_file.write_text(text)
raise SystemExit(0 if all(x['passed'] for x in results) else 1)
