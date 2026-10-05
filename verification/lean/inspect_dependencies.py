#!/usr/bin/env python3
"""Pre-gate Lean declaration-type and exact-axiom inspection (not an audit round).

The harness does not prove or assume any theorem. It invokes #check and
#print axioms against existing module objects. This is not an independent proof replay. No final release
claim is made, and pending roots remain explicitly pending in the inventory.
"""
import argparse,datetime,hashlib,json,os,pathlib,re,subprocess,sys
sys.dont_write_bytecode = True

REQUIRED_FINAL_ROLES = {
 'actual source-bound compact SOS identity',
 'instantiated bounded commuting-PVM upper identity',
 'universal arbitrary-dimensional tensor-product POVM upper bound',
 'complete canonical source decoding and exact-byte linkage',
 'final attained maximum/supremum theorem',
 'complete scalar multiplication/power evaluation soundness',
}
REQUIRED_SCALAR_DECLARATIONS = {'CGLMP5.Scalar.eval_mul','CGLMP5.Scalar.eval_pow'}

ALLOWED_AXIOM_BASENAMES = {'propext','Classical.choice','Quot.sound'}

def split_axiom_names(text):
 result=[];buf=[];depth=0;quoted=0
 for c in text:
  if c=='«':quoted+=1
  elif c=='»':quoted-=1
  elif not quoted:
   if c=='{':depth+=1
   elif c=='}':depth-=1
   elif c==',' and depth==0:
    if ''.join(buf).strip():result.append(''.join(buf).strip())
    buf=[];continue
  buf.append(c)
 if ''.join(buf).strip():result.append(''.join(buf).strip())
 return result

def forbidden_axioms(names):
 return [n for n in names if re.sub(r'\.\{.*\}$','',n) not in ALLOWED_AXIOM_BASENAMES]

def type_has_omissions(printed_type):
 return printed_type is not None and '⋯' in printed_type

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,cwd):
 r=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 return {'command':cmd,'exit_code':r.returncode,'output':r.stdout}
def snapshot(root):
 files=sorted(list((root/'lean'/'CGLMP5').rglob('*.lean'))+[root/'lean'/'CGLMP5.lean',root/'lean'/'lean-toolchain',root/'lean'/'lakefile.toml',root/'lean'/'lake-manifest.json'])
 entries={str(p.relative_to(root)):sha(p) for p in files if p.exists()}
 digest=hashlib.sha256(json.dumps(entries,sort_keys=True,separators=(',',':')).encode()).hexdigest()
 return {'digest':digest,'files':entries}

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--output',required=True,type=pathlib.Path)
 ap.add_argument('--inventory',type=pathlib.Path,default=pathlib.Path(__file__).with_name('declaration_inventory.json'))
 ap.add_argument('--trust-zero',action='store_true',help='Pass --trust=0 to the frontend. This does NOT recheck imported objects in pinned Lean; genuine replay is a separate leanchecker --fresh stage.')
 ap.add_argument('--expand-implicit-arguments',action='store_true',help='Also print every implicit application argument; very large instance trees can produce tens of megabytes per type. Quantified binders are printed in both modes.')
 ap.add_argument('--fail-if-pending',action='store_true',help='Completion gate: fail unless every requested root is present and inspected.')
 ap.add_argument('--skip-freshness-check',action='store_true',help='Inspect existing objects even if Lake cannot confirm freshness; status will say so.')
 args=ap.parse_args(); repo=pathlib.Path(__file__).resolve().parents[2]; lean=repo/'lean'; out=args.output.resolve()
 if args.fail_if_pending and args.skip_freshness_check:
  raise SystemExit('Final inspection cannot skip module freshness checks.')
 if out==repo or repo in out.parents:raise SystemExit('Inspection outputs must be outside the repository.')
 out.mkdir(parents=True,exist_ok=True)
 script_sha256=sha(pathlib.Path(__file__).resolve())
 inventory_sha256_before=sha(args.inventory)
 mapped_manifest=repo/'verification/lean/mapped_declarations.json'
 mapped_guard=repo/'verification/lean/check_mapped_inventory.py'
 mapped_manifest_sha256_before=sha(mapped_manifest)
 mapped_guard_sha256_before=sha(mapped_guard)
 inv=json.loads(args.inventory.read_text())
 if not isinstance(inv.get('declarations'),list) or not inv['declarations']:
  raise SystemExit('Missing or empty declaration inventory; inspection cannot pass.')
 missing_roles=REQUIRED_FINAL_ROLES-{d.get('role') for d in inv['declarations']}
 if missing_roles:raise SystemExit('Missing required final-root roles: '+', '.join(sorted(missing_roles)))
 for d in inv['declarations']:
  if d.get('status')=='ready' and (not isinstance(d.get('module'),str) or not isinstance(d.get('name'),str)
      or not d['module'].startswith('CGLMP5.') or not d['name'].startswith('CGLMP5.')):
   raise SystemExit('Invalid ready declaration entry: '+repr(d))
 mapped_coverage=None
 if args.fail_if_pending:
  from check_mapped_inventory import check as check_mapped_inventory
  mapped_coverage=check_mapped_inventory(repo,inventory=inv)
  if mapped_coverage['status']!='CONSISTENT':
   raise SystemExit('Mapped declaration coverage failed: '+ '; '.join(mapped_coverage['errors']))
 before=snapshot(repo)
 ready=[d for d in inv['declarations'] if d['status']=='ready']
 modules=sorted({d['module'] for d in ready}); freshness={}; admitted=[]
 for m in modules:
  obj=lean/'.lake/build/lib/lean'/pathlib.Path(*m.split('.')).with_suffix('.olean')
  src=lean/pathlib.Path(*m.split('.')).with_suffix('.lean')
  rec={'source_sha256':sha(src) if src.exists() else None,'object_sha256':sha(obj) if obj.exists() else None}
  if not obj.exists():rec['status']='missing-object'
  elif args.skip_freshness_check:rec['status']='existing-object-freshness-unchecked';admitted.append(m)
  else:
   check=run(['lake','--no-build','build',m],lean)
   (out/(m.replace('.','_')+'.freshness.log')).write_text(check['output'])
   rec['freshness_exit_code']=check['exit_code']
   rec['status']='lake-confirmed-current' if check['exit_code']==0 else 'not-confirmed-current'
   if check['exit_code']==0:admitted.append(m)
  freshness[m]=rec
 active=[d for d in ready if d['module'] in admitted]
 lines=[f'import {m}' for m in admitted]+['','set_option pp.universes true',f'set_option pp.explicit {str(args.expand_implicit_arguments).lower()}','set_option pp.fullNames true',
  'set_option pp.deepTerms true','set_option pp.proofs true','set_option pp.maxSteps 10000000','set_option maxRecDepth 20000','']
 line_map={}
 for d in active:
  lines.append(f'-- {d["role"]}')
  line_map[len(lines)+1]={'name':d['name'],'kind':'type'};lines.append('#check @'+d['name'])
  line_map[len(lines)+1]={'name':d['name'],'kind':'axioms'};lines.append('#print axioms '+d['name'])
  lines.append('')
 harness=out/'DependencyInspection.lean';harness.write_text('\n'.join(lines)+'\n')
 lean_command=['lake','env','lean','--json']
 if args.trust_zero:lean_command.append('--trust=0')
 lean_command.extend(['-DmaxRecDepth=200000','-DmaxHeartbeats=0'])
 lean_command.append(str(harness))
 result=run(lean_command,lean)
 (out/'lean_output.jsonl').write_text(result['output'])
 records={d['name']:{**d,'printed_type':None,'axiom_output':None,'axioms':None} for d in active};diagnostics=[]
 for line in result['output'].splitlines():
  try:event=json.loads(line)
  except json.JSONDecodeError:continue
  pos=event.get('pos',{});marker=line_map.get(pos.get('line'))
  if not marker:diagnostics.append(event);continue
  rec=records[marker['name']];message=event.get('message',event.get('data',''))
  if marker['kind']=='type':rec['printed_type']=message
  else:
   rec['axiom_output']=message
   if 'does not depend on any axioms' in message:rec['axioms']=[]
   else:
    match=re.search(r'depends on axioms:\s*\[([^\]]*)\]',message,re.S)
    if match:rec['axioms']=split_axiom_names(match.group(1))
 unexpected_axioms={name:forbidden_axioms(rec['axioms']) for name,rec in records.items() if rec['axioms'] is not None and forbidden_axioms(rec['axioms'])}
 omitted_types=[name for name,rec in records.items() if type_has_omissions(rec['printed_type'])]
 if args.fail_if_pending:
  missing_scalar=REQUIRED_SCALAR_DECLARATIONS-set(records)
  for name in sorted(missing_scalar):diagnostics.append({'severity':'error','message':'Required final scalar declaration missing: '+name})
 else:missing_scalar=set()
 after=snapshot(repo)
 inspection_inputs_changed=(inventory_sha256_before!=sha(args.inventory) or mapped_manifest_sha256_before!=sha(mapped_manifest) or mapped_guard_sha256_before!=sha(mapped_guard))
 receipt={'purpose':'pre-completion-gate dependency inspection; not a final audit round','timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'script_sha256':script_sha256,'inventory_sha256':inventory_sha256_before,'inventory_sha256_after':sha(args.inventory),'mapped_manifest_sha256':mapped_manifest_sha256_before,'mapped_manifest_sha256_after':sha(mapped_manifest),'mapped_guard_sha256':mapped_guard_sha256_before,'mapped_guard_sha256_after':sha(mapped_guard),'inspection_inputs_changed_during_run':inspection_inputs_changed,'mapped_reference_coverage':mapped_coverage,'harness_sha256':sha(harness),'source_snapshot_before':before,'source_snapshot_after':after,
  'source_changed_during_run':before['digest']!=after['digest'],'toolchain':run(['lean','--version'],lean),
  'lake':run(['lake','--version'],lean),'git_head':run(['git','rev-parse','HEAD'],repo),
  'module_objects':freshness,'lean_command':lean_command,'expand_implicit_application_arguments':args.expand_implicit_arguments,'lean_trust_setting':('0; frontend option only, imported objects not replayed' if args.trust_zero else 'default max; imported objects not replayed'),'imported_objects_kernel_replayed':False,'lean_exit_code':result['exit_code'],'diagnostics':diagnostics,'declarations':list(records.values()),
  'pending':[d for d in inv['declarations'] if d['status']!='ready']+[dict(d,status='pending-current-object') for d in ready if d['module'] not in admitted],
  'allowed_axiom_basenames':sorted(ALLOWED_AXIOM_BASENAMES),'unexpected_axioms':unexpected_axioms,'types_with_omissions':omitted_types,'missing_required_scalar_declarations':sorted(missing_scalar),'unparsed_declarations':[n for n,r in records.items() if r['printed_type'] is None or r['axioms'] is None]}
 (out/'inspection.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n')
 with (out/'TYPES_AND_AXIOMS.txt').open('w') as f:
  f.write(receipt['purpose']+'\nSource snapshot before: '+before['digest']+'\nLean exit: '+str(result['exit_code'])+'\n\n')
  for r in records.values():f.write(r['name']+'\n'+str(r['printed_type'])+'\n'+str(r['axiom_output'])+'\n\n')
  f.write('PENDING\n')
  for d in receipt['pending']:f.write(json.dumps(d,ensure_ascii=False)+'\n')
 print(json.dumps({'output':str(out),'lean_exit_code':result['exit_code'],'inspected':len(records),'unparsed':receipt['unparsed_declarations'],'types_with_omissions':omitted_types,'pending':len(receipt['pending']),'source_changed':receipt['source_changed_during_run']},indent=2))
 if inspection_inputs_changed or unexpected_axioms or omitted_types or missing_scalar or result['exit_code'] or receipt['unparsed_declarations'] or (args.fail_if_pending and (receipt['pending'] or receipt['source_changed_during_run'])):return 1
 return 0
if __name__=='__main__':raise SystemExit(main())
