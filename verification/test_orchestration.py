#!/usr/bin/env python3
"""Execute synthetic adversarial processes against the actual replay guard."""
import argparse, hashlib, json, os, subprocess, sys
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.root=a.root.resolve();a.output=a.output.resolve()
    if a.output.exists():raise RuntimeError('new output required')
    a.output.mkdir(parents=True);fixture=a.output/'fixture.py';fixture.write_text("import argparse,json\nfrom pathlib import Path\np=argparse.ArgumentParser();p.add_argument('--root');p.add_argument('--output',type=Path);p.add_argument('--mode');a=p.parse_args()\nif a.mode != 'incomplete':\n a.output.write_text(json.dumps({'status':'FAIL' if a.mode=='false_success' else 'PASS','nonzero_residual_count':1 if a.mode=='nonzero_residual' else 0}))\nprint('FAIL with intentional exit0' if a.mode=='false_success' else 'fixture completed')\n")
    guard=a.root/'verification/guarded_replay.py';rows=[]
    for name in ['valid','false_success','nonzero_residual','incomplete','wrong_argument','stale_receipt']:
        out=a.output/name
        if name=='stale_receipt':out.mkdir();(out/'result.json').write_text('{"status":"PASS","nonzero_residual_count":0}')
        cmd=[sys.executable,str(guard),'--root',str(a.root/'artifact_v0.1.1'),'--output',str(out),'--script',str(fixture),'--expect','nonzero_residual_count=0','--','--mode',name]
        if name=='wrong_argument':cmd+=['--unsupported-argument']
        p=subprocess.run(cmd,text=True,capture_output=True);(a.output/(name+'.stdout')).write_text(p.stdout);(a.output/(name+'.stderr')).write_text(p.stderr)
        expected=0 if name=='valid' else 1;passed=(p.returncode==0)==(expected==0)
        r={'test':name,'command':cmd,'returncode':p.returncode,'status':'PASS' if passed else 'FAIL','expected':'accept mathematical PASS with zero residual' if name=='valid' else 'reject','stdout_sha256':sha(a.output/(name+'.stdout')),'stderr_sha256':sha(a.output/(name+'.stderr'))}
        if (out/'receipt.json').exists():r['child_guard_receipt']=json.loads((out/'receipt.json').read_text())
        if name=='stale_receipt':passed=passed and 'STALE_OUTPUT_DIRECTORY' in p.stderr;r['status']='PASS' if passed else 'FAIL'
        rows.append(r)
    result={'status':'PASS' if all(r['status']=='PASS' for r in rows) else 'FAIL','guard_sha256':sha(guard),'fixture_sha256':sha(fixture),'tests':rows};(a.output/'SUMMARY.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));raise SystemExit(result['status']!='PASS')
if __name__=='__main__':main()
