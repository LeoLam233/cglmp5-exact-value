#!/usr/bin/env python3
"""Exact binary64 feasibility diagnostics, distinct from repaired representatives."""
import argparse, hashlib, json, sys, os
from pathlib import Path
from fractions import Fraction as F
if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE') not in (None,'','0'):raise SystemExit('REFUSED_OPTIMIZED_EXECUTION')
import numpy as np

def exact_unitarity(q):
    d=len(q);zs=[[(F(float(z.real)),F(float(z.imag))) for z in row] for row in q]
    failures=[]
    for i in range(d):
        for j in range(d):
            re=sum(zs[k][i][0]*zs[k][j][0]+zs[k][i][1]*zs[k][j][1] for k in range(d))-int(i==j)
            im=sum(zs[k][i][0]*zs[k][j][1]-zs[k][i][1]*zs[k][j][0] for k in range(d))
            if re or im:failures.append({'entry':[i,j],'real':str(re),'imag':str(im)})
    return {'exact_nonzero_QstarQ_minus_I_entries':len(failures),'first_exact_residual':failures[0] if failures else None,'floating_frobenius_residual':float(np.linalg.norm(q.conj().T@q-np.eye(d)))}
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    paths=[next(a.root.rglob('strongest_supplement_candidate.npz')),a.root/'outputs/RUN_RECEIPTS/attainment/a06_optimizer_replay.npz'];rows=[]
    for p in paths:
        v=np.load(p);bases=[q for key in ['X','Y'] for q in v[key]]; checks=[exact_unitarity(q) for q in bases]
        if not any(q['exact_nonzero_QstarQ_minus_I_entries'] for q in checks):raise RuntimeError('expected raw binary64 nonunitarity absent; reassess')
        rows.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'arrays':{k:list(v[k].shape) for k in v.files},'basis_checks':checks,'raw_binary64_exactly_unitary':False})
    status_path=a.root/'outputs/RUN_RECEIPTS/attainment/a06_optimizer_replay.json';statuses=json.loads(status_path.read_text());cases=statuses['cases']
    if len(cases)!=31 or not all('success' in c and 'message' in c for c in cases):raise RuntimeError('optimizer statuses incomplete')
    result={'status':'PASS','raw_candidates':rows,'historical_optimizer_status_sha256':hashlib.sha256(status_path.read_bytes()).hexdigest(),'historical_optimizer_attempts':len(cases),'historical_successful_terminations':sum(c['success'] for c in cases),'scope':'Fresh exact Fraction tests of preserved raw binary64 arrays. Historical solver statuses are identified as historical, never rerun optimizer evidence. Exact repaired physical representatives are distinct objects verified separately; neither sampling nor optimization proves a global bound.'}
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
