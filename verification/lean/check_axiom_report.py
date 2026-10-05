#!/usr/bin/env python3
"""Compare fresh exact type/axiom capture with the frozen inventory/report.

This validates receipt/report consistency only. It never infers kernel validity
or scientific correctness from JSON; those are separate completion-gate stages.
"""
import sys
sys.dont_write_bytecode = True
import argparse, hashlib, json, pathlib, re
from inspect_dependencies import split_axiom_names, forbidden_axioms
ROOT=pathlib.Path(__file__).resolve().parents[2]
ROW=re.compile(r'^\| `(CGLMP5[^`]+)` \| `(CGLMP5[^`]+)` \| `\[([^\]]*)\]` \|$',re.M)

def compare(receipt, inventory, report):
    errors=[]
    entries=inventory.get('declarations',[])
    captured=receipt.get('declarations',[])
    if not isinstance(entries,list) or not all(isinstance(d,dict) for d in entries):
        return {'status':'INCONSISTENT','errors':['Malformed inventory declaration list'],'scientific_pass_inferred':False}
    if not isinstance(captured,list) or not all(isinstance(d,dict) for d in captured):
        return {'status':'INCONSISTENT','errors':['Malformed captured declaration list'],'scientific_pass_inferred':False}
    expected={d.get('name'):d for d in entries};actual={d.get('name'):d for d in captured}
    rows=ROW.findall(report)
    for line in report.splitlines():
        if re.match(r'^\s*\|\s*`?CGLMP5',line) and ROW.fullmatch(line) is None:
            errors.append('Malformed declaration table row: '+line)
    printed={n:{'module':m,'axioms':split_axiom_names(a)} for n,m,a in rows}
    if not entries or len(expected)!=len(entries):errors.append('Empty or duplicate inventory')
    if len(actual)!=len(captured):errors.append('Duplicate captured declaration')
    if len(printed)!=len(rows):errors.append('Duplicate report declaration')
    if set(actual)!=set(expected):errors.append('Captured declaration set differs from inventory')
    if set(printed)!=set(expected):errors.append('Report declaration set differs from inventory')
    if any(d.get('status')!='ready' for d in entries):errors.append('Inventory has pending declarations')
    if receipt.get('lean_exit_code')!=0:errors.append('Inspection Lean invocation did not succeed')
    if receipt.get('source_changed_during_run') is not False:errors.append('Inspection source snapshot was not stable')
    if receipt.get('inspection_inputs_changed_during_run') is not False:errors.append('Inspection inventory/map inputs were not stable')
    for field in ['pending','unparsed_declarations','types_with_omissions','missing_required_scalar_declarations']:
        if receipt.get(field)!=[]:errors.append('Inspection has missing or nonempty '+field)
    if receipt.get('unexpected_axioms')!={}:errors.append('Inspection has unexpected or missing axiom classification')
    if receipt.get('mapped_reference_coverage',{}).get('status')!='CONSISTENT':errors.append('Mapped reference coverage was not checked')
    for name in sorted(set(expected)&set(actual)&set(printed)):
        e,a,p=expected[name],actual[name],printed[name]
        if a.get('module')!=e.get('module') or p['module']!=e.get('module'):errors.append('Declaration module mismatch: '+name)
        axioms=a.get('axioms')
        if not isinstance(axioms,list) or not all(isinstance(x,str) for x in axioms):errors.append('Unparsed axiom set: '+name)
        elif forbidden_axioms(axioms):errors.append('Unexpected axiom: '+name)
        elif p['axioms']!=axioms:errors.append('Exact report axiom set mismatch: '+name)
        typ=a.get('printed_type')
        if not isinstance(typ,str) or not typ.strip() or '⋯' in typ:errors.append('Missing or omitted printed type: '+name)
    return {'status':'CONSISTENT' if not errors else 'INCONSISTENT','errors':errors,
            'inventory_count':len(entries),'captured_count':len(captured),'report_count':len(rows),
            'scientific_pass_inferred':False,'scope':'Exact inventory/type-presence/axiom-table consistency. Proof replay, provenance, semantic validation and audits remain separate requirements.'}

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--inspection',required=True,type=pathlib.Path);p.add_argument('--output',required=True,type=pathlib.Path);a=p.parse_args()
    out=a.output.resolve()
    if out.is_relative_to(ROOT):raise SystemExit('Comparison receipt must be external to candidate tree')
    if out.exists():raise SystemExit('Refusing to overwrite existing comparison evidence')
    ip=ROOT/'verification/lean/declaration_inventory.json';rp=ROOT/'AXIOM_AUDIT.md';sp=ROOT/'verification/lean/inspect_dependencies.py'
    receipt=json.loads(a.inspection.read_text());result=compare(receipt,json.loads(ip.read_text()),rp.read_text())
    if receipt.get('inventory_sha256')!=sha(ip):result['errors'].append('Inspection inventory hash is stale')
    if receipt.get('script_sha256')!=sha(sp):result['errors'].append('Inspection harness script hash is stale')
    for field,file in [('mapped_manifest_sha256','mapped_declarations.json'),('mapped_guard_sha256','check_mapped_inventory.py')]:
        if receipt.get(field)!=sha(ROOT/'verification/lean'/file):result['errors'].append('Inspection mapped coverage input hash is stale: '+file)
    snapshot=receipt.get('source_snapshot_after',{}).get('files',{})
    if not snapshot:result['errors'].append('Missing inspected source snapshot')
    for name,digest in snapshot.items():
        path=ROOT/name
        if not path.resolve().is_relative_to(ROOT) or not path.is_file() or sha(path)!=digest:
            result['errors'].append('Inspected source changed or missing: '+name)
    result['status']='CONSISTENT' if not result['errors'] else 'INCONSISTENT'
    result['inputs']={'inspection_sha256':sha(a.inspection),'inventory_sha256':sha(ip),'axiom_report_sha256':sha(rp),'inspection_script_sha256':sha(sp)}
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));return 0 if result['status']=='CONSISTENT' else 1
if __name__=='__main__':raise SystemExit(main())
