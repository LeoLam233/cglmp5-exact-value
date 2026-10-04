"""Independent physical/convention audit. No supplied verifier imports.

Only frozen audit_view scientific inputs are read. Algebra is Q[z,mu] modulo
Phi20(z) and the branch-specific cubic for mu. Fractions are exact.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse, hashlib, json, itertools, time

HERE = Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('input_directory', nargs='?', type=Path,
                    default=HERE.parent.parent/'audit_view')
args=parser.parse_args()
VIEW = args.input_directory.resolve()
LOG = []
def record(name, **data):
    entry = dict(test=name, **data)
    LOG.append(entry)
    print(json.dumps(entry), flush=True)

Z0 = (F(0),)*8
Z1 = (F(1),)+(F(0),)*7
def ca(a,b): return tuple(x+y for x,y in zip(a,b))
def cn(a): return tuple(-x for x in a)
def cs(a,r): return tuple(x*r for x in a)
def cm(a,b):
    out = [F(0)]*15
    for j,x in enumerate(a):
        if x:
            for k,y in enumerate(b):
                if y: out[j+k] += x*y
    for j in range(14,7,-1):
        v=out[j]
        if v:
            out[j-2]+=v; out[j-4]-=v; out[j-6]+=v; out[j-8]-=v
    return tuple(out[:8])
Z=(F(0),F(1))+(F(0),)*6
ZPOW=[Z1]
for _ in range(1,21): ZPOW.append(cm(ZPOW[-1],Z))
assert ZPOW[20] == Z1
def zp(k): return ZPOW[k%20]
def cc(a):
    out=Z0
    for j,x in enumerate(a):
        if x: out=ca(out,cs(zp(-j),x))
    return out
S=ca(cs(ca(zp(2),zp(-2)),2),cn(Z1))
U=cs(ca(zp(1),zp(-1)),2)
CI=zp(5)
assert cm(S,S)==cs(Z1,5)
assert cm(U,U)==ca(cs(Z1,10),cs(S,2))
assert cm(CI,CI)==cn(Z1)
assert cc(S)==S and cc(U)==U
assert cs(ca(U,cm(CI,ca(S,cn(Z1)))),F(1,4))==Z
assert cm(Z,cc(Z))==Z1
record('cyclotomic_arithmetic', degree=8, Phi20='z^8-z^6+z^4-z^2+1', z20_equals_one=True)

E0=(Z0,Z0,Z0)
E1=(Z1,Z0,Z0)
MU=(Z0,Z1,Z0)
def ec(a): return (a,Z0,Z0)
def ea(a,b): return tuple(ca(x,y) for x,y in zip(a,b))
def en(a): return tuple(cn(x) for x in a)
def es(a,r): return tuple(cs(x,r) for x in a)
C1=ca(cs(Z1,4),cs(S,F(-4,5)))
C0=ca(cs(Z1,4),cs(S,F(-8,5)))
def em(a,b):
    out=[Z0]*5
    for j,x in enumerate(a):
        for k,y in enumerate(b): out[j+k]=ca(out[j+k],cm(x,y))
    for j in (4,3):
        v=out[j]
        out[j-1]=ca(out[j-1],cm(v,S))
        out[j-2]=ca(out[j-2],cm(v,C1))
        out[j-3]=ca(out[j-3],cm(v,C0))
    return tuple(out[:3])
def ep(a,k):
    out=E1
    for _ in range(k): out=em(out,a)
    return out
def eadj(a): return tuple(cc(x) for x in a)

def w2(x,y,a,b):
    """Twice the weight, from the standard eight-event expression alone."""
    out=0
    for k,weight in ((0,2),(1,1)):
        if (x,y)==(0,0) or (x,y)==(1,1):
            out += weight*((a-b-k)%5==0)
            out -= weight*((a-b+k+1)%5==0)
        elif (x,y)==(1,0):
            out += weight*((b-a-k-1)%5==0)
            out -= weight*((b-a+k)%5==0)
        elif (x,y)==(0,1):
            out += weight*((b-a-k)%5==0)
            out -= weight*((b-a+k+1)%5==0)
    return out

for x,y,a,b in itertools.product(range(2),range(2),range(5),range(5)):
    residue = ((a-b)%5 if (x,y) in ((0,0),(1,1)) else
               (b-a-1)%5 if (x,y)==(1,0) else (b-a)%5)
    assert w2(x,y,a,b)==2-residue
classic=[]
for a0,b0,a1,b1 in itertools.product(range(5),repeat=4):
    val=sum(w2(x,y, (a0,a1)[x],(b0,b1)[y]) for x,y in itertools.product(range(2),repeat=2))
    ds=(a0,b0,(a1+1)%5,(b1+1)%5)
    residues=[(ds[0]-ds[1])%5,(ds[1]-ds[2])%5,(ds[2]-ds[3])%5,(ds[3]-ds[0]-1)%5]
    assert val==8-sum(residues) and sum(residues)%5==4
    classic.append(val)
assert max(classic)==4
record('standard_event_mapping', exact_pair_events=100, deterministic_assignments=625, classical_maximum='2')

C={}
for k in range(5):
    C[k]=Z0
    for r in range(5): C[k]=ca(C[k],cs(zp(-4*k*r),F(2-r,10)))
assert C[0]==Z0
for k in range(1,5):
    assert cm(cs(ca(Z1,cn(zp(-4*k))),2),C[k])==Z1
    assert C[5-k]==cc(C[k])
record('DFT', exact_coefficients=5, reciprocal_formula_checked_by_multiplication=True, conjugation=True)

# All four Fourier bases: direct inner products, not a Bell ansatz.
for r in range(4):
    offset=(0,1,2,-1)[r]
    sign=1 if r%2==0 else -1
    for a,b in itertools.product(range(5),repeat=2):
        dot=Z0
        for j in range(5): dot=ca(dot,cs(zp(4*sign*j*(b-a)),F(1,5)))
        assert dot==(Z1 if a==b else Z0)
record('Fourier_bases', exact_inner_products=100, orthonormal=True)

# Matrices U_r^k built directly by summing Fourier projectors with outcome phases.
LOCAL={}
for r,k in itertools.product(range(4),range(5)):
    shift=1 if r in (2,3) else 0
    offset=(0,1,2,-1)[r]
    sign=1 if r%2==0 else -1
    mat={}
    for j,l in itertools.product(range(5),repeat=2):
        c=Z0
        for a in range(5):
            c=ca(c,cs(zp(4*k*(a+shift)+(j-l)*(4*sign*a+offset)),F(1,5)))
        if c!=Z0: mat[j,l]=c
    LOCAL[r,k]=mat
    assert len(mat)==5

def madd(dst, row, col, value):
    key=(row,col); dst[key]=ca(dst.get(key,Z0),value)
def clean(dst): return {key:v for key,v in dst.items() if v!=Z0}

# Entire Bell matrix directly from probability weights and projectors.
Bprob={}
for j,m,l,n in itertools.product(range(5),repeat=4):
    value=Z0
    for x,y,a,b in itertools.product(range(2),range(2),range(5),range(5)):
        q=w2(x,y,a,b)
        if q:
            exponent=(j-l)*(4*a+2*x)+(m-n)*(-4*b+(1 if y==0 else -1))
            value=ca(value,cs(zp(exponent),F(q,50)))
    if value!=Z0: Bprob[5*j+m,5*l+n]=value

# Entire Bell matrix separately from D-encoded generator polynomial.
Bpoly={}
for r,s in ((0,1),(1,2),(2,3),(3,0)):
    for k in range(1,5):
        coef=cm(C[k],zp(-4*k)) if (r,s)==(3,0) else C[k]
        am=LOCAL[r,k] if r%2==0 else LOCAL[s,(-k)%5]
        bm=LOCAL[s,(-k)%5] if r%2==0 else LOCAL[r,k]
        for (j,l),av in am.items():
            for (m,n),bv in bm.items(): madd(Bpoly,5*j+m,5*l+n,cm(coef,cm(av,bv)))
Bpoly=clean(Bpoly)
assert Bpoly==Bprob
for (r,c),value in Bprob.items(): assert Bprob.get((c,r),Z0)==cc(value)
for (r,c) in Bprob:
    assert ((r//5-r%5)-(c//5-c%5))%5==0
record('Bell_matrix', dimension=25, entries_checked=625, nonzero_entries=len(Bprob), probability_equals_generator_polynomial=True, Hermitian=True, all_five_difference_sectors_invariant=True)

f1=cs(cm(U,ca(cs(Z1,5),cn(S))),F(1,20))
f2=cs(ca(S,cn(Z1)),F(1,2))
f3=cs(cm(U,S),F(1,10))
f4=cs(ca(S,Z1),F(1,2))
assert cm(f1,cs(U,F(1,2)))==Z1
fs={1:f1,2:f2,3:f3,4:f4}
for j,l in itertools.product(range(5),repeat=2):
    assert Bprob.get((6*j,6*l),Z0)==(Z0 if j==l else fs[abs(j-l)])
record('compressed_matrix', exact_entries_checked=25, Toeplitz_offdiagonals=True, diagonal_zero=True)

h=ca(f1,f3)
quad=ca(ca(cm(f2,f4),cn(cm(h,h))),cn(cs(ca(cm(f2,f2),cm(f1,f1)),2)))
constant=ca(ca(cs(cm(f4,cm(f1,f1)),2),cs(cm(f2,cm(f2,f2)),2)),cn(cs(cm(h,cm(f1,f2)),4)))
assert ca(f2,f4)==S and quad==cn(C1) and constant==cn(C0)
record('symmetric_three_by_three_characteristic', coefficient_equalities_exact=True,
       polynomial='t^3-s*t^2-(4-4*s/5)*t-(4-8*s/5)')

D=ea(em(MU,ea(MU,en(ec(f2)))),en(ec(cs(cm(f1,f1),2))))
A=ea(em(MU,ec(ca(f1,f3))),ec(cs(cm(f1,f2),2)))
g_edge=em(MU,D)
g_adj=em(MU,A)
g_mid=es(ea(em(ec(f2),D),em(ec(f1),A)),2)
G=[E0]*25
for idx,c in zip((0,6,12,18,24),(g_edge,g_adj,g_mid,g_adj,g_edge)): G[idx]=c
BG=[E0]*25
for (r,c),value in Bprob.items(): BG[r]=ea(BG[r],em(ec(value),G[c]))
residual=[ea(v,en(em(MU,g))) for v,g in zip(BG,G)]
assert all(v==E0 for v in residual)
record('attaining_state', full_coordinates_checked=25, exact_eigen_residual_zero=True, denominator_cleared='G=mu*D*(1,a,b,a,1)', no_compression_assumption=True)

# Sextic, radical branch and independent rational isolation.
def pmul(a,b):
    o=[F(0)]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        for k,y in enumerate(b): o[j+k]+=x*y
    return o
pa=[16,96,144,0,-65,0,5]
AA=[-20,-20,0,5]; BB=[-8,-4,5]
lhs=pmul(AA,AA); bb=pmul(BB,BB)
for k,q in enumerate(bb): lhs[k]-=5*q
assert lhs==[5*q for q in pa]
def peval(t): return 5*t**6-65*t**4+144*t**2+96*t+16
lo,hi=F(3),F(31,10)
assert peval(lo)<0<peval(hi)
for _ in range(256):
    mid=(lo+hi)/2
    if peval(mid)<0: lo=mid
    else: hi=mid
mu_poly=ea(ea(es(ep(MU,6),5),es(ep(MU,4),-65)),ea(ea(es(ep(MU,2),144),es(MU,96)),es(E1,16)))
assert mu_poly==E0
record('root', polynomial_identity=True, cubic_implies_sextic=True, rational_lower=str(lo), rational_upper=str(hi), uniqueness_argument='p prime = t^3*(30t^2-260)+288t+96 >0 for t>=3')

# Independent necessary consistency attack on every serialized SOS polynomial:
# any positive SOS at an attained vector must have R*G=R^dagger*G=0.
serial=json.loads((VIEW/'SOS14.json').read_text(encoding='utf8'))
SB=ec(S); UB=ec(U); IB=ec(CI); XB=es(MU,5)
scalar_basis=[]
for ix in range(24):
    aa=ix%2; bb=(ix//2)%3; ccx=(ix//6)%2; ee=ix//12
    scalar_basis.append(em(em(ep(SB,aa),ep(XB,bb)),em(ep(UB,ccx),ep(IB,ee))))
def decode(obj):
    assert len(obj['n'])==24 and int(obj['d'])>0
    value=E0
    for q,basis in zip(obj['n'],scalar_basis):
        if int(q): value=ea(value,es(basis,F(int(q),int(obj['d']))))
    return value
def local_action(v,r,k):
    o=[E0]*25
    for (j,l),c in LOCAL[r,k%5].items():
        for h in range(5):
            dest,src=(5*j+h,5*l+h) if r%2==0 else (5*h+j,5*h+l)
            o[dest]=ea(o[dest],em(ec(c),v[src]))
    return o
def word_action(v,word):
    for r,k in reversed(word): v=local_action(v,r,k)
    return v
coefficient_count=0
for term in serial['terms']:
    rg=[E0]*25; rdg=[E0]*25
    for node in term['polynomial']:
        coefficient_count+=1
        coeff=decode(node['coefficient']); word=node['word']
        vg=word_action(G,word)
        vd=word_action(G,[[r,-k] for r,k in reversed(word)])
        rg=[ea(o,em(coeff,v)) for o,v in zip(rg,vg)]
        rdg=[ea(o,em(eadj(coeff),v)) for o,v in zip(rdg,vd)]
    assert all(v==E0 for v in rg), term['id']+' R G'
    assert all(v==E0 for v in rdg), term['id']+' Rdag G'
record('SOS_attainment_consistency', polynomials_checked=len(serial['terms']), coefficients_checked=coefficient_count, full_vector_tests=2*len(serial['terms']), all_exactly_annihilate=True, does_not_establish_universal_identity=True)

# Finite realization of the explicit common-space Naimark construction.
import numpy as np
rng=np.random.default_rng(5012026)
def sqrt_pos(m):
    v,w=np.linalg.eigh(m)
    return (w*np.sqrt(np.maximum(v,0)))@w.conj().T
def povm(d):
    raw=[]
    for _ in range(5):
        z=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)); raw.append(z@z.conj().T)
    total=sum(raw); val,vec=np.linalg.eigh(total)
    inv=(vec*(1/np.sqrt(val)))@vec.conj().T
    return [inv@r@inv for r in raw]
def common_dilation(sets):
    d=len(sets[0][0]); kid=4*d; dim=d+2*kid; groups=[]
    for x,ee in enumerate(sets):
        V=np.concatenate([sqrt_pos(e) for e in ee],axis=0)
        left,_,_=np.linalg.svd(V,full_matrices=True)
        W=np.column_stack((V,left[:,d:]))
        idx=list(range(d))+list(range(d+x*kid,d+(x+1)*kid))
        other=list(range(d+(1-x)*kid,d+(2-x)*kid))
        pp=[]
        for a in range(5):
            local=W[a*d:(a+1)*d,:].conj().T@W[a*d:(a+1)*d,:]
            big=np.zeros((dim,dim),complex); big[np.ix_(idx,idx)]=local
            if a==0: big[np.ix_(other,other)]=np.eye(kid)
            pp.append(big)
        groups.append(pp)
    return groups
ea_p=[povm(2),povm(2)]; eb_p=[povm(3),povm(3)]
da=common_dilation(ea_p); db=common_dilation(eb_p)
err=0.0
for sets,ext,d in ((ea_p,da,2),(eb_p,db,3)):
    for x in range(2):
        err=max(err,float(np.max(np.abs(sum(ext[x])-np.eye(len(ext[x][0]))))))
        for a,b in itertools.product(range(5),repeat=2):
            target=ext[x][a] if a==b else np.zeros_like(ext[x][a])
            err=max(err,float(np.max(np.abs(ext[x][a]@ext[x][b]-target))))
        for a in range(5): err=max(err,float(np.max(np.abs(ext[x][a][:d,:d]-sets[x][a]))))
orig=rng.normal(size=6)+1j*rng.normal(size=6); orig/=np.linalg.norm(orig)
ext=np.zeros((18,27),complex); ext[:2,:3]=orig.reshape(2,3); ext=ext.ravel()
prob_err=0.0
for x,y,a,b in itertools.product(range(2),range(2),range(5),range(5)):
    origp=np.vdot(orig,np.kron(ea_p[x][a],eb_p[y][b])@orig)
    newp=np.vdot(ext,np.kron(da[x][a],db[y][b])@ext)
    prob_err=max(prob_err,float(abs(origp-newp)))
assert err<1e-12 and prob_err<1e-12
record('finite_Naimark_sanity', seed=5012026, original_local_dimensions=[2,3], dilated_local_dimensions=[18,27], algebra_error=err, joint_probability_error=prob_err, cases=100, infinite_case_requires_analytic_argument=True)

# Mutation controls: deliberately wrong sign/shift must be detected.
controls=[]
for mutation in ('remove_last_phase','reverse_last_phase','remove_A1_outcome_shift','remove_B1_outcome_shift'):
    bad={}
    for r,s in ((0,1),(1,2),(2,3),(3,0)):
        for k in range(1,5):
            lastphase=-4*k
            if mutation=='remove_last_phase': lastphase=0
            if mutation=='reverse_last_phase': lastphase=4*k
            coef=cm(C[k],zp(lastphase)) if (r,s)==(3,0) else C[k]
            am=LOCAL[r,k] if r%2==0 else LOCAL[s,(-k)%5]
            bm=LOCAL[s,(-k)%5] if r%2==0 else LOCAL[r,k]
            ak=k if r%2==0 else -k
            bk=-k if r%2==0 else k
            if mutation=='remove_A1_outcome_shift' and 2 in (r,s):
                am={key:cm(v,zp(-4*ak)) for key,v in am.items()}
            if mutation=='remove_B1_outcome_shift' and 3 in (r,s):
                bm={key:cm(v,zp(-4*bk)) for key,v in bm.items()}
            for (j,l),av in am.items():
                for (m,n),bv in bm.items(): madd(bad,5*j+m,5*l+n,cm(coef,cm(av,bv)))
    bad=clean(bad)
    mismatch=sum(bad.get(key,Z0)!=Bprob.get(key,Z0) for key in set(bad)|set(Bprob))
    assert mismatch>0
    controls.append(dict(mutation=mutation,mismatched_entries=mismatch))
record('sign_shift_mutation_controls', controls=controls)

identity=json.loads((VIEW/'INPUT_IDENTITY.json').read_text(encoding='utf8'))
actual={name:hashlib.sha256((VIEW/name).read_bytes()).hexdigest() for name in identity}
assert actual==identity
record('input_hashes', expected_match=True, hashes=actual,
       semantic_exposure=['AUDIT_CONTRACT.md','INPUT_IDENTITY.json','PROOF.md','ROOT_EMBEDDING.md','SOS14.json'],
       byte_only_exposure=['EXACT_KERNELS.json','EXACT_SOS_CANDIDATE.json','POSITIVITY_CERTIFICATE.json','verify_independent.py','verify_sos14.py','verify_statement.py'])
(HERE/'results.json').write_text(json.dumps(LOG,indent=2)+'\n',encoding='utf8')
record('complete', result_file=str(HERE/'results.json'))
