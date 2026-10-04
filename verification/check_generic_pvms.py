#!/usr/bin/env python3
"""Exact rational, complete five-outcome PVMs above and below dimension five.
Householder orthogonal columns grouped mod 5 prove PSD as sums vv^T; all
orthogonality/idempotence/completeness relations checked in rational arithmetic.
These finite fixtures are diagnostics, not the universal upper-bound proof.
"""
import argparse,hashlib,json,random,sys,os
from pathlib import Path
if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE') not in (None,'','0'):raise SystemExit('REFUSED_OPTIMIZED_EXECUTION')
import sympy as S

def require(v,m):
    if not v:raise RuntimeError(m)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();rng=random.Random(2026100410);rows=[]
    for da,db in [(2,3),(6,7),(5,8)]:
        sides=[]
        for d in (da,db):
            families=[]
            for setting in range(2):
                v=S.Matrix([rng.randrange(1,10) for _ in range(d)]);Q=S.eye(d)-2*v*v.T/(v.T*v)[0];require(Q.T*Q==S.eye(d),'orthogonality');effects=[sum((Q[:,j]*Q[:,j].T for j in range(a,d,5)),S.zeros(d)) for a in range(5)]
                require(sum(effects,S.zeros(d))==S.eye(d),'completeness');require(all(E==E.T and E*E==E for E in effects),'PVM positivity/idempotence');require(all(effects[i]*effects[j]==S.zeros(d) for i in range(5) for j in range(5) if i!=j),'outcome orthogonality');families.append(effects)
            nc=sum(1 for x in families[0] for y in families[1] if x*y!=y*x);require(nc>0,'noncommuting settings required');sides.append({'dimension':d,'settings':2,'outcomes_per_setting':5,'all_columns_grouped':True,'exact_completeness':True,'exact_orthogonal_projections':True,'PSD_witness':'each effect is an explicitly summed outer product of rational orthonormal columns','ranks':[[E.rank() for E in f] for f in families],'nonzero_setting_commutators':nc})
        rows.append({'dimensions':[da,db],'parties':sides})
    result={'status':'PASS','seed':2026100410,'arithmetic':'SymPy rational matrices','sympy_version':S.__version__,'rows':rows,'measurement_families':12,'exact_five_outcome_effects':60,'scope':'Finite generic same-party noncommutation and exact physical admissibility controls; no finite-dimensional restriction or global-bound inference.','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
