#!/usr/bin/env python3
"""Exact checks of hard-coded formulas corresponding to PROOF.md; standard library.
Does not parse or semantically verify prose. Document bytes are bound by receipt hashes.
This is a statement/data consistency audit, not a third independent arithmetic engine.
"""
from pathlib import Path
from fractions import Fraction
import argparse,json,time
import verify_independent as v
from strict_schema import load_document,require_normal_python
from verification_receipt import receipt,run_cli

def conv(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out

def verify(root):
    require_normal_python();root=Path(root);st=time.monotonic();d,di=load_document(root/'SOS14.json')
    # Polynomial A(t)^2-5 B(t)^2=5 p(t), ascending coefficient order.
    aa=conv([-20,-20,0,5],[-20,-20,0,5]);bb=conv([-8,-4,5],[-8,-4,5]);bb+=[0]*(len(aa)-len(bb))
    v.ensure([a-5*b for a,b in zip(aa,bb)]==[80,480,720,0,-325,0,25], 'printed root bridge polynomial')
    ib=v.interval_basis(d['embedding_boxes']);gamma=list(map(v.load_scalar,d['gamma']))
    f1=(v.U*(5-v.S)).rational_scale(1,20)
    f2=(v.S-1).rational_scale(1,2)
    f3=(v.U*v.S).rational_scale(1,10)
    f4=(v.S+1).rational_scale(1,2)
    v.ensure(f1*v.U==2 and 2*v.S*f3==v.U,'printed reciprocal-free Fourier entries')
    denom=v.MU*(v.MU-f2)-2*f1*f1;num=v.MU*(f1+f3)+2*f1*f2
    v.ensure(gamma[0]==1 and gamma[4]==1 and gamma[1]==gamma[3],'printed palindromic Schmidt vector')
    v.ensure(gamma[1]*denom==num,'printed a formula')
    v.ensure(v.MU*gamma[2]==2*(f2+f1*gamma[1]),'printed b formula')
    v.positive(denom-v.C(4),ib,'printed denominator greater than four')
    fk=[v.ZERO,f1,f2,f3,f4]
    v.ensure(all(sum(fk[abs(i-j)]*gamma[j] for j in range(5))==v.MU*gamma[i] for i in range(5)),'printed reduced Bell matrix eigenvector')
    # Orthogonality of each local Fourier basis: offsets cancel in overlaps.
    overlaps=0
    for a in range(5):
        for b in range(5):
            val=sum(v.ZS[(4*j*(a-b))%20] for j in range(5)).rational_scale(1,5)
            v.ensure(val==(1 if a==b else 0),'Fourier basis orthonormality');overlaps+=1
    return {'status':'PASS','root_bridge_polynomial_exact':True,'printed_Schmidt_formulas_match_certificate':True,'denominator_strictly_greater_than_4':True,'reduced_eigenvector_equations':5,'Fourier_orthonormality_pairs':overlaps,'scope':'Printed-statement/data correspondence; reuses independent checker arithmetic, not a separate external audit.','elapsed_seconds':time.monotonic()-st,'receipt':receipt('verify_statement.py',root,[di],['hard-coded root bridge polynomial','hard-coded Schmidt formulas','denominator greater than four','reduced eigenvector and Fourier orthonormality; prose itself not parsed'])}
if __name__=='__main__':
    a=argparse.ArgumentParser(description=__doc__);a.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--output',type=Path);x=a.parse_args()
    raise SystemExit(run_cli(lambda:verify(x.root),x.output))
