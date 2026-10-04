#!/usr/bin/env python3
"""Deliberate falsification tests of the final exact proof interfaces.
Mutations exist only in memory; the original certificates are never altered.
"""
import copy,json,time
from pathlib import Path
from fractions import Fraction
import verify_independent as v
R=Path(__file__).resolve().parent
K=json.loads((R/'EXACT_KERNELS.json').read_text());C=json.loads((R/'EXACT_SOS_CANDIDATE.json').read_text());P=json.loads((R/'POSITIVITY_CERTIFICATE.json').read_text())
results=[]
def rejected(name, fn):
    try: fn()
    except (ArithmeticError,ValueError,KeyError) as e:
        results.append({'test':name,'expected':'reject','result':'PASS','reason':str(e)})
    else: raise AssertionError('Corruption escaped detection: '+name)

def perturb(o):
    o['n'][0]=str(int(o['n'][0])+1)

def negate(o): o['n']=[str(-int(x)) for x in o['n']]

start=time.monotonic()
c=copy.deepcopy(C);perturb(c['H']['1'][0][0]);rejected('one integer in H changed',lambda:v.verify_words(K,c))
k=copy.deepcopy(K);entry=next(a for row in k['kernels']['6']['E'] for a in row if any(map(int,a['n'])));perturb(entry);rejected('one E coefficient changed',lambda:v.verify_words(k,C))
k=copy.deepcopy(K)
for row in k['kernels']['1']['E']:
    for a in row:a['n']=['0']*24
rejected('extra positive block1 incorrectly dropped',lambda:v.verify_words(k,C))
p=copy.deepcopy(P);c=copy.deepcopy(C)
for row in c['H']['9']:
    for a in row:negate(a)
for a in p['blocks']['9']['D']:negate(a)
rejected('consistent negative H/LDL sign flip',lambda:v.verify_positive(c,p))
p=copy.deepcopy(P);p['embedding_boxes']['sqrt5']['lower']['numerator']='-3'
rejected('wrong sqrt5 branch',lambda:v.verify_positive(C,p))
p=copy.deepcopy(P);p['embedding_boxes']['mu']['lower']={'numerator':'-4','denominator':'1'};p['embedding_boxes']['mu']['upper']={'numerator':'-3','denominator':'1'}
rejected('wrong mu root interval',lambda:v.verify_positive(C,p))
original=v.make_bell
def bad_bell():
    good=original();out={}
    for w,c in good.items():
        if {r for r,k in w}=={0,3}:
            k=next(k for r,k in w if r==3)
            c=c*v.ZS[(8*k)%20] # omega^(+k) instead of omega^(-k)
        out[w]=c
    return out
v.make_bell=bad_bell
try:rejected('wraparound Fourier phase sign reversed',lambda:v.verify_words(K,C))
finally:v.make_bell=original
oldmu=v.MU;v.MU=oldmu-v.C(Fraction(1,10**12))
try:rejected('claimed upper bound lowered by 10^-12',lambda:v.verify_words(K,C))
finally:v.MU=oldmu
ib=v.interval_basis(P['embedding_boxes']);k=copy.deepcopy(K)
k['gamma']=[K['gamma'][0]]*5
rejected('maximally entangled state substituted for optimizer',lambda:v.verify_physical(k,ib))
originalstep=v.step
def badstep(r,j):
    out,e=originalstep(r,j)
    return out,(e+1)%20 if r==3 and j==4 else e
v.step=badstep
try:rejected('physical wraparound phase corrupted',lambda:v.verify_physical(K,ib))
finally:v.step=originalstep
# Stored PASS flags are not mathematical inputs: deleting all top-level flags
# and display spectra must not affect the actual mathematical checks.
c=copy.deepcopy(C);p=copy.deepcopy(P)
for key in ['status','coefficient_zero_residual','numerical_eigenvalues_not_a_positivity_proof']:c.pop(key,None)
p['all_pivots_strictly_positive']=False
v.verify_words(K,c);v.verify_positive(c,p)
results.append({'test':'stored PASS flags ignored','expected':'mathematical checks still pass','result':'PASS'})
# Deliberately test the noncommutative word convention with same-party
# alternating operators; it must not accidentally commute Alice's settings.
ensure=v.ensure
ensure(v.canon(((0,1),(2,1)))!=v.canon(((2,1),(0,1))),'same-party settings wrongly commute')
ensure(v.canon(((0,1),(1,1)))==v.canon(((1,1),(0,1))),'cross-party settings should commute')
ensure(v.canon(((0,1),(2,1),(2,4),(0,4)))==(),'nested local cancellation failed')
results.append({'test':'same-party noncommutativity and cross-party commutativity','result':'PASS'})
out={'status':'ALL_TESTS_PASSED','tests':results,'count':len(results),'mutated_source_files':False,'elapsed_seconds':time.monotonic()-start,'scope':'Same-agent adversarial verifier tests, not external audit or proof of verifier infallibility.'}
(R/'KILL_TESTS.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
