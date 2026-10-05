#!/usr/bin/env python3
"""Read-only production-module graph check using build_lean_clean.py's policy.
This is build preparation, not an adversarial audit or a proof/build PASS.
"""
import argparse,datetime,hashlib,json,pathlib,re,subprocess

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',required=True,type=pathlib.Path);a=ap.parse_args()
 repo=pathlib.Path(__file__).resolve().parents[2];lean=repo/'lean';out=a.output.resolve()
 if out==repo or repo in out.parents:raise SystemExit('Graph receipts must be outside the repository.')
 out.mkdir(parents=True,exist_ok=True)
 files=[lean/'CGLMP5.lean']+sorted((lean/'CGLMP5').rglob('*.lean'))
 modules={p.relative_to(lean).with_suffix('').as_posix().replace('/','.'):p for p in files}
 texts={m:p.read_text() for m,p in modules.items()};hashes={m:hashlib.sha256(t.encode()).hexdigest() for m,t in texts.items()}
 imports={m:[x for line in t.splitlines() if line.startswith('import ') for x in line[7:].split()] for m,t in texts.items()}
 proj={m:[x for x in xs if x.startswith('CGLMP5')] for m,xs in imports.items()}
 missing=[{'module':m,'import':x} for m,xs in proj.items() for x in xs if x not in modules]
 state={};stack=[];cycles=[];order=[]
 def visit(m):
  if m not in modules:return
  if state.get(m)==2:return
  if state.get(m)==1:
   cycles.append(stack[stack.index(m):]+[m]);return
  state[m]=1;stack.append(m)
  for n in proj[m]:visit(n)
  stack.pop();state[m]=2;order.append(m)
 for m in modules:visit(m)
 reverse={m:[] for m in modules}
 for m,xs in proj.items():
  for x in xs:
   if x in reverse:reverse[x].append(m)
 reachable=set()
 def reach(m):
  if m in reachable or m not in modules:return
  reachable.add(m)
  for x in proj[m]:reach(x)
 reach('CGLMP5')
 candidates=[]
 for m,p in modules.items():
  if re.search(r'(Pilot|Probe|Scratch|Legacy|Attempt)',m):
   candidates.append({'module':m,'path':str(p.relative_to(repo)),'sha256':hashes[m], 'imported_by':reverse[m],'reachable_from_library_root':m in reachable,'status':'owner review required; not automatically retired'})
 external_missing=[];external_resolution={};resolver_error=None
 roots=[lean/'.lake/packages'/p['name'] for p in json.loads((lean/'lake-manifest.json').read_text())['packages']]
 try:
  prefix=pathlib.Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip())
  core_roots=[prefix/'src/lean',prefix/'lib/lean']
 except (OSError,subprocess.CalledProcessError) as e:
  core_roots=[];resolver_error=str(e)
 for x in sorted({x for xs in imports.values() for x in xs if not x.startswith('CGLMP5')}):
  relative=pathlib.Path(*x.split('.'));resolved_paths=[]
  for root in roots+core_roots:
   for ext in ('.lean','.olean'):
    path=root/relative.with_suffix(ext)
    if path.exists():resolved_paths.append(str(path))
  external_resolution[x]=resolved_paths
  if not resolved_paths:
   external_missing.extend({'module':m,'import':x} for m,xs in imports.items() if x in xs)
 changed=[m for m,p in modules.items() if not p.exists() or sha(p)!=hashes[m]]
 final_files=[lean/'CGLMP5.lean']+sorted((lean/'CGLMP5').rglob('*.lean'))
 initial_paths={str(p.relative_to(repo)) for p in files}
 final_paths={str(p.relative_to(repo)) for p in final_files}
 added_paths=sorted(final_paths-initial_paths)
 removed_paths=sorted(initial_paths-final_paths)
 result={'purpose':'dependency-only build-hygiene preparation; no final audit or proof replay',
 'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'policy_script_sha256':sha(repo/'scripts/build_lean_clean.py'),
 'module_count':len(modules),'project_edge_count':sum(map(len,proj.values())),'source_hashes':hashes,'imports':imports,'topological_order':order,
 'missing_project_imports':missing,'cycles':cycles,'missing_external_imports':external_missing,'external_import_resolution':external_resolution,'external_resolver_error':resolver_error,
 'unreachable_from_library_root':sorted(set(modules)-reachable),'unimported_modules':sorted(m for m,v in reverse.items() if not v and m!='CGLMP5'),
 'prototype_named_candidates':candidates,'source_changed_during_scan':changed,
 'source_files_added_during_scan':added_paths,'source_files_removed_during_scan':removed_paths,
 'status':'GRAPH_FAIL' if missing or cycles or external_missing or resolver_error else ('UNSTABLE_SNAPSHOT' if changed or added_paths or removed_paths else 'GRAPH_COMPLETE')}
 (out/'MODULE_GRAPH.json').write_text(json.dumps(result,indent=2)+'\n')
 (out/'TOPOLOGICAL_MODULE_ORDER.txt').write_text('\n'.join(order)+'\n')
 summary={k:result[k] for k in ['status','module_count','project_edge_count','missing_project_imports','cycles','missing_external_imports','external_resolver_error','source_changed_during_scan','source_files_added_during_scan','source_files_removed_during_scan']}
 summary['prototype_named_candidates']=candidates;summary['unreachable_count']=len(result['unreachable_from_library_root']);print(json.dumps(summary,indent=2))
 return 1 if result['status']!='GRAPH_COMPLETE' else 0
if __name__=='__main__':raise SystemExit(main())
