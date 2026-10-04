#!/usr/bin/env python3
"""Normal-Python component guard; never derives mathematical PASS from exit 0.

The child must support --root and --output. The output directory must be new.
Additional dotted semantic fields can be required with --expect field=JSON.
"""
import sys, os
if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE') not in (None,'','0'):raise SystemExit('REFUSED_OPTIMIZED_EXECUTION')
import argparse, datetime, hashlib, json, platform, subprocess, time
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(v,m):
    if not v:raise RuntimeError(m)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--script',type=Path,required=True);ap.add_argument('--expect',action='append',default=[]);ap.add_argument('args',nargs=argparse.REMAINDER);a=ap.parse_args()
    root=a.root.resolve();out=a.output.resolve();script=a.script.resolve();require(not out.exists(),'STALE_OUTPUT_DIRECTORY: output must not already exist');out.mkdir(parents=True);result=out/'result.json'
    args=a.args[1:] if a.args[:1]==['--'] else a.args;command=[sys.executable,str(script),'--root',str(root),'--output',str(result),*args];env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'};env.pop('PYTHONOPTIMIZE',None)
    stamp=datetime.datetime.now(datetime.timezone.utc).isoformat();start=time.monotonic();p=subprocess.run(command,cwd=out,env=env,text=True,capture_output=True);(out/'stdout.txt').write_text(p.stdout);(out/'stderr.txt').write_text(p.stderr)
    row={'command':command,'cwd':str(out),'started_utc':stamp,'seconds':time.monotonic()-start,'returncode':p.returncode,'python':sys.version,'platform':platform.platform(),'optimization_flag':sys.flags.optimize,'PYTHONOPTIMIZE':os.environ.get('PYTHONOPTIMIZE'),'script_sha256':sha(script),'input_sha256':{q.name:sha(q) for q in sorted(root.glob('*.json'))},'stdout_sha256':sha(out/'stdout.txt'),'stderr_sha256':sha(out/'stderr.txt'),'status':'FAIL'}
    try:
        require(p.returncode==0,'CHILD_NONZERO_EXIT');require(result.exists(),'INCOMPLETE_OUTPUT');v=json.loads(result.read_text());requirements=['status="PASS"']+a.expect
        for item in requirements:
            name,expected=item.split('=',1);actual=v
            for k in name.split('.'):actual=actual[k]
            require(actual==json.loads(expected),'SEMANTIC_MISMATCH:'+name)
        row['semantic_result']=v;row['result_sha256']=sha(result);row['status']='PASS'
    except Exception as e:row['failure']=str(e)
    (out/'receipt.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row,indent=2));raise SystemExit(0 if row['status']=='PASS' else 1)
if __name__=='__main__':main()
