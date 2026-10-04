#!/usr/bin/env python3
"""Verify the fourteen-anticommutator presentation; no Gram data or solvers.
Requires only SOS14.json and verify_independent.py in addition to this file.
"""
from pathlib import Path
import json,time,argparse
from verify_independent import ZERO,MU,load_scalar,canon,star,word_product,make_bell,interval_basis,positive,ensure,verify_physical

def verify(root,quiet=False):
    st=time.monotonic();d=json.loads((root/'SOS14.json').read_text());ib=interval_basis(d['embedding_boxes'])
    ensure(len(d['terms'])==14,'wrong anticommutator count');acc={};terms=0
    for t in d['terms']:
        weight=load_scalar(t['weight']);positive(weight,ib,'weight '+t['id'])
        poly=[]
        for term in t['polynomial']:
            raw=tuple(map(tuple,term['word']));w=canon(raw)
            ensure(raw==w and len(w)<=2,'unexpected unreduced or high-degree term')
            ensure(len(w)<2 or (w[0][0]%2==0 and w[1][0]%2==1),'term not 1+AB')
            poly.append((w,load_scalar(term['coefficient'])))
        ensure(len({w for w,c in poly})==len(poly),'duplicate polynomial words')
        for w,a in poly:
            for v,b in poly:
                t1=word_product(star(w),v); t2=word_product(w,star(v))
                acc[t1]=acc.get(t1,ZERO)+weight*a.conjugate()*b
                acc[t2]=acc.get(t2,ZERO)+weight*a*b.conjugate()
        terms+=len(poly)
    rhs={w:-c for w,c in make_bell().items()};rhs[()]=MU
    universe=set(acc)|set(rhs)
    ensure(all(acc.get(w,ZERO)==rhs.get(w,ZERO) for w in universe),'anticommutator polynomial residual is not zero')
    ph=verify_physical({'gamma':d['gamma']},ib)
    out={'status':'PASS','anticommutators':14,'explicit_polynomial_coefficients':terms,'expanded_word_support':len(universe),'upper_bound_exact':True,'weights_strictly_positive':True,'physical_lower_bound':ph,'elapsed_seconds':time.monotonic()-st}
    if not quiet: print(json.dumps(out,indent=2))
    return out
if __name__=='__main__':
    a=argparse.ArgumentParser(description=__doc__);a.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--output',type=Path);x=a.parse_args();v=verify(x.root)
    if x.output:x.output.write_text(json.dumps(v,indent=2))
