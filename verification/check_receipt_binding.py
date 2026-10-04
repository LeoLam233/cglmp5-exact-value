#!/usr/bin/env python3
"""Independently inspect every fresh successful hardening receipt's actual bytes."""
import argparse,hashlib,json
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(v,m):
    if not v:raise RuntimeError(m)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True,help='completed hardening run');ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();summary=json.loads((a.root/'SUMMARY.json').read_text());require(summary['status']=='PASS','hardening summary not pass');rows=[]
    for r in summary['rows']:
        v=r.get('semantic_result')
        if not v:continue
        receipt=v['receipt'];root=Path(r['command'][r['command'].index('--root')+1]);require(receipt['enforced_target_sha256']==summary['enforced_target_sha256'],'theorem receipt drift')
        for x in receipt['inputs']:require(sha(root/x['file'])==x['sha256'],'input hash stale')
        for name,h in receipt['source_sha256'].items():require(sha(root/name)==h,'source hash stale')
        for name,h in receipt['document_sha256'].items():require(sha(root/name)==h,'doc hash stale')
        if r['label']=='unknown_theorem_id':require('theorem_id' in receipt['inputs'][0]['unverified_top_level_annotations'],'unknown theorem_id not explicitly annotative')
        if r['label']=='declared_support':require(any('words' in x['unverified_top_level_annotations'] for x in receipt['inputs'] if x['file']=='EXACT_KERNELS.json'),'declared support not annotative')
        if r['label']=='cached_status':require(any('status' in x['unverified_top_level_annotations'] for x in receipt['inputs'] if x['file']=='EXACT_SOS_CANDIDATE.json'),'cached status not annotative')
        if r['label']=='proof_text':require(receipt['document_sha256']['PROOF.md']!=sha(a.root/'baseline/PROOF.md'),'mutated proof hash not changed')
        if r['label']=='explicit_zero':require(v['stored_polynomial_records']==165 and v['nonzero_polynomial_coefficients']==164,'stored and nonzero counts conflated')
        rows.append({'label':r['label'],'entrypoint':r['entrypoint'],'status':'PASS','input_hashes_checked':len(receipt['inputs']),'source_hashes_checked':len(receipt['source_sha256']),'document_hashes_checked':len(receipt['document_sha256'])})
    result={'status':'PASS','successful_receipts_checked':len(rows),'rows':rows,'scope':'Byte bindings and explicit enforced/annotative distinctions, not prose theorem verification.'};a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
