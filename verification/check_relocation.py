#!/usr/bin/env python3
"""Fresh relocated core execution, with spaces in paths and unrelated cwd."""
import argparse,hashlib,importlib.metadata,json,os,platform,shutil,subprocess,sys
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(v,m):
    if not v:raise RuntimeError(m)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);ap.add_argument('--output',required=True,type=Path);a=ap.parse_args();a.root=a.root.resolve();a.output=a.output.resolve();require(not a.output.exists(),'new output required');a.output.mkdir(parents=True)
    relocated=a.output/'relocated release with spaces'/'artifact_v0.1.1';shutil.copytree(a.root/'artifact_v0.1.1',relocated,ignore=shutil.ignore_patterns('__pycache__','*.pyc'));cwd=a.output/'unrelated working directory';cwd.mkdir();env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'};env.pop('PYTHONOPTIMIZE',None);rows=[]
    for ep in ['validate_integer_encoding.py','verify_sos14.py','verify_statement.py','verify_independent.py','kill_tests.py']:
        cmd=[sys.executable,str(relocated/ep),'--root',str(relocated),'--output',str(a.output/(ep+'.result.json'))];p=subprocess.run(cmd,cwd=cwd,env=env,text=True,capture_output=True);(a.output/(ep+'.stdout')).write_text(p.stdout);(a.output/(ep+'.stderr')).write_text(p.stderr);require(p.returncode==0,ep+' exit failure');x=json.loads((a.output/(ep+'.result.json')).read_text());require(x['status']==('ALL_TESTS_PASSED' if ep=='kill_tests.py' else 'PASS'),ep+' semantic status');rows.append({'command':cmd,'returncode':p.returncode,'status':x['status'],'result':ep+'.result.json','result_sha256':sha(a.output/(ep+'.result.json')),'stdout_sha256':sha(a.output/(ep+'.stdout')),'stderr_sha256':sha(a.output/(ep+'.stderr'))})
    copied={str(p.relative_to(relocated)):sha(p) for p in relocated.rglob('*') if p.is_file()}
    for name,h in copied.items():require(sha(a.root/'artifact_v0.1.1'/name)==h,'relocation changed source/input '+name)
    result={'status':'PASS','fresh_core_entrypoints':5,'relocated_root':str(relocated),'cwd':str(cwd),'copied_input_source_sha256':copied,'runs':rows,'environment':{'python':sys.version,'platform':platform.platform(),'optimize':sys.flags.optimize,'dependency_versions':{n:importlib.metadata.version(n) for n in ['numpy','sympy','scipy','mpmath']}},'seed_scope':'Scientific diagnostic seeds are explicit in byte-preserved Phase-B scripts: generic tensor10459, sampling20261004, completeness4242, wrong-embedding31337/918, finite-field and normalizer seeds recorded by their source hashes. Exact core arithmetic is deterministic.'};(a.output/'SUMMARY.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'PASS','fresh_core_entrypoints':5,'copied_files':len(copied)}))
if __name__=='__main__':main()
