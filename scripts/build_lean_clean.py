#!/usr/bin/env python3
"""Reproducible, resource-bounded whole-project Lean replay followed by plain lake build.
All project modules are compiled in topological order; no project source is skipped.
Dependencies are pinned by lake-manifest.json. Receipts must be outside the Git tree.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,platform,re,shutil,subprocess,sys,time
from lean_replay_paths import validate_checkout_paths
ap=argparse.ArgumentParser();ap.add_argument('--receipt-dir',required=True,type=Path);ap.add_argument('--clean-project',action='store_true');ap.add_argument('--require-clean-git',action='store_true');args=ap.parse_args()
root=Path(__file__).resolve().parents[1];lean=root/'lean';out=args.receipt_dir.resolve()
path_validation=validate_checkout_paths(root)
if out==root or root in out.parents:raise SystemExit('Receipts must be outside the repository to preserve the audited tree')
out.mkdir(parents=True,exist_ok=True)
def call(cmd,cwd=root):return subprocess.check_output(cmd,cwd=cwd,text=True).strip()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
status=call(['git','status','--porcelain'])
if args.require_clean_git and status:raise SystemExit('Candidate Git tree is not clean')
head=call(['git','rev-parse','HEAD']);tree=call(['git','rev-parse','HEAD^{tree}'])
version=call(['lean','--version'],lean);lake=call(['lake','--version'],lean)
if 'version 4.34.1,' not in version:raise SystemExit('Unexpected Lean toolchain: '+version)
dep=json.loads((lean/'lake-manifest.json').read_text());dep_receipts=[]
for p in dep['packages']:
 d=lean/'.lake/packages'/p['name'];actual=call(['git','rev-parse','HEAD'],d);dirty=call(['git','status','--porcelain'],d)
 if actual!=p['rev'] or dirty:raise SystemExit('Dependency is not the pinned clean source: '+p['name'])
 dep_receipts.append({'name':p['name'],'revision':actual})
files=[lean/'CGLMP5.lean']+sorted((lean/'CGLMP5').rglob('*.lean'))
modules={p.relative_to(lean).with_suffix('').as_posix().replace('/','.'):p for p in files}
imports={m:[x for line in p.read_text().splitlines() if line.startswith('import ') for x in line[7:].split() if x.startswith('CGLMP5')] for m,p in modules.items()}
order=[];visiting=set();visited=set()
def visit(m):
 if m in visited:return
 if m not in modules:raise RuntimeError('Missing project module '+m)
 if m in visiting:raise RuntimeError('Import cycle '+m)
 visiting.add(m)
 for n in imports[m]:visit(n)
 visiting.remove(m);visited.add(m);order.append(m)
for m in modules:visit(m)
before={p.relative_to(root).as_posix():sha(p) for p in files}
cache=lean/'.lake/build'
if args.clean_project and cache.exists():
 if cache.is_symlink():raise SystemExit('Refusing a symlink project build cache')
 shutil.rmtree(cache)
env=os.environ.copy()
for key in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(key,None)
env['LEAN_NUM_THREADS']='1'
receipt={'status':'RUNNING','platform':platform.platform(),'uname':{k:v for k,v in platform.uname()._asdict().items() if k!='node'},'python':sys.version,'python_executable':sys.executable,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'head':head,'tree':tree,'initial_git_status':status,'clean_project':args.clean_project,'lean':version,'lake':lake,'dependencies':dep_receipts,'source_hashes':before,'module_order':order,'external_build_cache':False,'path_validation':path_validation,'inherited_lean_search_paths_cleared':True,'results':[]}
def save(): (out/'BUILD_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
save()
for i,m in enumerate(order):
 t=time.monotonic();cmd=['lake','--no-cache','build','+'+m]
 r=subprocess.run(cmd,cwd=lean,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 log=f'{i:04d}-{m}.log';(out/log).write_text(r.stdout);row={'module':m,'command':cmd,'exit':r.returncode,'seconds':time.monotonic()-t,'log':log};receipt['results'].append(row);save();print(json.dumps(row),flush=True)
 if r.returncode:receipt['status']='FAIL';save();raise SystemExit(r.returncode)
r=subprocess.run(['lake','build'],cwd=lean,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(out/'FINAL_LAKE_BUILD.log').write_text(r.stdout)
after={p.relative_to(root).as_posix():sha(p) for p in files};final_status=call(['git','status','--porcelain']);unchanged=before==after and final_status==status and call(['git','rev-parse','HEAD'])==head and call(['git','rev-parse','HEAD^{tree}'])==tree
receipt.update(status='PASS' if r.returncode==0 and unchanged else 'FAIL',final_lake_build_exit=r.returncode,source_unchanged=unchanged,final_git_status=final_status,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());save();print(json.dumps({k:receipt[k] for k in ['status','tree','source_unchanged','final_lake_build_exit']}),flush=True)
raise SystemExit(0 if receipt['status']=='PASS' else 1)
