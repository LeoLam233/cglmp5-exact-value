#!/usr/bin/env python3
"""Characteristic-zero proper-quotient/commutator control; published arithmetic.
A valid identity survives abelianization; abelianized checking alone misses an
injected same-party commutator. This reuses the hardened scalar engine, not an
independent arithmetic implementation or a verifier for malformed JSON.
"""
import argparse,hashlib,json,sys,os
from pathlib import Path
if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE') not in (None,'','0'):raise SystemExit('REFUSED_OPTIMIZED_EXECUTION')
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();artifact=a.root/'artifact_v0.1.1';sys.path.insert(0,str(artifact));import verify_independent as v;import strict_schema as s
    raw,meta=s.load_document(artifact/'SOS14.json');terms=[(v.load_scalar(t['weight']),[(tuple(map(tuple,p['word'])),v.load_scalar(p['coefficient'])) for p in t['polynomial']]) for t in raw['terms']]
    def quotient(w):
        ex=[0]*4
        for r,k in w:ex[r]=(ex[r]+k)%5
        return tuple((r,ex[r]) for r in (0,2,1,3) if ex[r])
    def residual(ts,abelian=False):
        acc={};normal=quotient if abelian else v.canon
        def put(w,c):w=normal(w);acc[w]=acc.get(w,v.ZERO)+c
        for d,poly in ts:
            for w,c in poly:
                for z,b in poly:put(v.star(w)+z,d*c.conjugate()*b);put(w+v.star(z),d*c*b.conjugate())
        for w,c in v.make_bell().items():put(w,c)
        put((),-v.MU);return {w:c for w,c in acc.items() if c}
    before=residual(terms);quot=residual(terms,True);modified=[(d,list(p)) for d,p in terms];modified[0][1].extend([(((0,1),(2,1)),v.ONE),(((2,1),(0,1)),-v.ONE)]);bad=residual(modified);blind=residual(modified,True)
    if before or quot or not bad or blind:raise RuntimeError('proper quotient/noncommutator invariant failed')
    result={'status':'PASS','characteristic':0,'baseline_NC_nonzero_residuals':len(before),'baseline_abelian_nonzero_residuals':len(quot),'commutator_mutant_NC_nonzero_residuals':len(bad),'commutator_mutant_abelian_nonzero_residuals':len(blind),'control':'Add U0U2-U2U0 to the first square in memory; correct abelianization hides it, NC characteristic-zero arithmetic rejects it.','input_sha256':meta['sha256'],'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in artifact.glob('*.py')},'scope':'Reuses published cyclotomic arithmetic; complements independent A04 exact compact/Gram replay.'};a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
