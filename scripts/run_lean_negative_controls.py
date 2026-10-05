#!/usr/bin/env python3
"""Run pre-gate semantic mutation fixtures in isolated copied files.

This is not one of the final adversarial audit rounds. No production source is mutated.
The distinct actual SOS coefficient-corruption runner is required separately.
"""
import sys
sys.dont_write_bytecode = True
from negative_control_support import ReplayGuard, add_replay_arguments
from lean_rejection import FIXTURE_KINDS, classify_rejection
from pathlib import Path
import argparse, datetime, hashlib, json, subprocess, tempfile, time
p=argparse.ArgumentParser();p.add_argument('--lake',required=True);p.add_argument('--timeout',type=int,default=180);add_replay_arguments(p);a=p.parse_args()
repo=Path(__file__).resolve().parents[1];lean=repo/'lean';base=repo/'verification/lean_negative_controls'
guard=ReplayGuard(repo,a,base/'runs');stamp=guard.stamp;out=guard.out
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def manifest():return {str(f.relative_to(lean)):sha(f) for f in sorted((lean/'CGLMP5').glob('*.lean'))}
start=manifest(); results=[]
files=[base/'fixtures/positive_control.lean']+sorted(f for f in (base/'fixtures').glob('*.lean') if f.name!='positive_control.lean')
actual_names={f.stem for f in files}; expected_names=set(FIXTURE_KINDS)|{'positive_control'}
if actual_names!=expected_names:
 raise RuntimeError('Fixture coverage differs from reviewed cases; missing='+str(sorted(expected_names-actual_names))+' unexpected='+str(sorted(actual_names-expected_names)))
for f in files:
 guard.check(f.stem+':before')
 with tempfile.TemporaryDirectory(prefix='cglmp-negative-') as td:
  copied=Path(td)/f.name;copied.write_bytes(f.read_bytes());begin=time.monotonic()
  try:r=subprocess.run([a.lake,'env','lean',str(copied)],cwd=lean,text=True,capture_output=True,timeout=a.timeout);code=r.returncode;log=r.stdout+r.stderr;timed=False
  except subprocess.TimeoutExpired as e:code=None;log=(e.stdout or b'').decode() if isinstance(e.stdout,bytes) else (e.stdout or '');log+='\nTIMEOUT';timed=True
  (out/(f.stem+'.log')).write_text(log)
  guard.check(f.stem+':after')
  positive=f.stem=='positive_control'
  diagnostic=None if positive else classify_rejection(log,code,f.name,FIXTURE_KINDS[f.stem],timed_out=timed,expected_count=1)
  ok=(code==0 and not timed) if positive else diagnostic['accepted']
  bad=False if positive else bool(diagnostic['blocked_markers'] or diagnostic['unparsed_error_lines'])
  results.append(dict(name=f.stem,fixture_sha256=sha(f),expected='compile_success' if positive else 'expected_proof_rejection',exit_code=code,timeout=timed,unrelated_error=bad,inspected_diagnostic=diagnostic,passed=ok,seconds=round(time.monotonic()-begin,3)))
  print(f.stem, 'PASS' if ok else 'FAIL',code,flush=True)
  if positive and not ok:break
end=manifest();version=subprocess.run([a.lake,'env','lean','--version'],cwd=lean,text=True,capture_output=True).stdout.strip()
receipt=dict(kind='precompletion_semantic_mutation_controls_not_final_audit',utc=stamp,lean_version=version,toolchain=(lean/'lean-toolchain').read_text().strip(),lake_manifest_sha256=sha(lean/'lake-manifest.json'),source_manifest_start=start,source_manifest_end=end,source_changed=start!=end,results=results,pending_hooks=guard.metadata()['pending_hooks'],final_audit_round=None,candidate_gate_eligible=False,status='PASS' if all(r['passed'] for r in results) and len(results)==len(files) else 'FAIL')
guard.check('end');receipt['frozen_replay']=guard.metadata()
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print('Receipt:',out/'receipt.json',flush=True)
raise SystemExit(0 if receipt['status']=='PASS' else 1)
