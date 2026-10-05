#!/usr/bin/env python3
"""Shadow-import mutation of a canonical coefficient; preserved source chunks must reject it."""
import sys
sys.dont_write_bytecode = True
from negative_control_support import ReplayGuard, add_replay_arguments
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,subprocess,tempfile,time
p=argparse.ArgumentParser();p.add_argument('--lake',required=True);add_replay_arguments(p);a=p.parse_args()
repo=Path(__file__).resolve().parents[1];leanroot=repo/'lean';tool=Path(a.lake).with_name('lean')
basepath=subprocess.check_output([a.lake,'env','printenv','LEAN_PATH'],cwd=leanroot,text=True).strip()
basepath=':'.join(str((leanroot/part).resolve()) if not Path(part).is_absolute() else part for part in basepath.split(':'))
guard=ReplayGuard(repo,a,repo/'verification/lean_negative_controls/source_binding_runs');stamp=guard.stamp;out=guard.out
names=['CertificateTerm00Data.lean','CertificateChunkData00.lean','CertificateChunk00C00.lean'];sources={n:(leanroot/'CGLMP5'/n).read_text() for n in names}
data=sources[names[0]];match=re.search(r'(⟨\[\(1, 1\)\], ⟨\[)(-?\d+)',data)
if match is None:raise SystemExit('Expected canonical coefficient location was not found')
old=match.group(2);new=str(int(old)+1);mut=data[:match.start(2)]+new+data[match.end(2):]
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
results=[]
for mode,source in [('original',data),('mutated',mut)]:
 with tempfile.TemporaryDirectory(prefix='cglmp-source-binding-') as td:
  td=Path(td);(td/'CGLMP5').mkdir()
  # Lean resolves a namespace at its first root, so shadow the complete local object namespace.
  # Imported dependencies are immutable symlinks; only the three tested modules are recompiled.
  blocked={Path(n).stem for n in names}
  for dep in (leanroot/'.lake/build/lib/lean/CGLMP5').iterdir():
   if dep.is_file() and dep.name.split('.')[0] not in blocked:
    (td/'CGLMP5'/dep.name).symlink_to(dep.resolve())
  env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env['LEAN_PATH']=str(td)+':'+basepath;env['LEAN_NUM_THREADS']='1';runs=[]
  for n in names:
   guard.check(mode+':'+n+':before')
   s=source if n==names[0] else sources[n]
   if n==names[0]:s+="\nnamespace CGLMP5.CertificateSource\nexample : (term00.polynomial[0]'(by decide)).coefficient.valid := by decide +kernel\nend CGLMP5.CertificateSource\n"
   (out/(mode+'_'+n)).write_text(s)
   f=td/'CGLMP5'/n;f.write_text(s);start=time.monotonic();r=subprocess.run([str(tool),'-R',str(td),'-o',str(f.with_suffix('.olean')),str(f)],cwd=td,env=env,text=True,capture_output=True)
   guard.check(mode+':'+n+':after')
   log=r.stdout+r.stderr;(out/f'{mode}_{n}.log').write_text(log);runs.append(dict(module=n,exit_code=r.returncode,seconds=round(time.monotonic()-start,3),compiled_input_sha256=sha(s),compiled_input_file=mode+'_'+n))
   print(mode,n,r.returncode,flush=True)
   if r.returncode:break
  ok=len(runs)==3 and all(x['exit_code']==0 for x in runs[:2]) and ((runs[-1]['exit_code']==0) if mode=='original' else runs[-1]['exit_code']==1)
  if mode=='mutated':
   expected_rejection=(log.count(': error:')==1 and 'CertificateChunk00C00.lean:' in log and 'Tactic `decide` proved that the proposition' in log and 'chunkScalar00C00.decode = some term00.polynomial[0].coefficient' in log and 'is false' in log)
   if not expected_rejection or any(z in log.lower() for z in ['unknown','object file','import','invalid header','no such file','memory','timeout','maximum recursion','heartbeats','interrupted']):ok=False
  results.append(dict(mode=mode,passed=ok,runs=runs))
receipt=dict(kind='kernel_source_decode_corruption_precompletion_not_final_audit',old_numerator=old,new_numerator=new,original_data_sha256=sha(data),mutated_data_sha256=sha(mut),source_sha256={n:sha(s) for n,s in sources.items()},lean_version=subprocess.check_output([str(tool),'--version'],text=True).strip(),lake_manifest_sha256=hashlib.sha256((leanroot/'lake-manifest.json').read_bytes()).hexdigest(),results=results,frozen_replay=guard.metadata(),status='PASS' if all(x['passed'] for x in results) else 'FAIL',scope='Source binding only. A distinct actual SOS coefficient corruption test remains required.')
guard.check('end');receipt['frozen_replay']=guard.metadata()
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print('Receipt:',out/'receipt.json',flush=True)
raise SystemExit(0 if receipt['status']=='PASS' else 1)
