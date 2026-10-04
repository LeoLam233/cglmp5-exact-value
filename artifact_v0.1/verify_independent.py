#!/usr/bin/env python3
"""Read-only certificate verifier using Python's standard library only.

This implementation DOES NOT import the discovery code, numerical solvers,
original tower arithmetic, its word reducer, or its positivity routines.
Arithmetic uses the different basis z^a x^b (0<=a<8, 0<=b<3), with
Phi_20(z)=z^8-z^6+z^4-z^2+1=0 and x=5*mu.  The verifier needs only three
JSON certificate files.  Flags and numerical spectra stored in them are
ignored.  Invocation: python verify_independent.py [--root DIRECTORY]
                         [--output PATH] [--skip-physical]
"""
from __future__ import annotations
import argparse, json, math, time
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
from itertools import product


def ensure(test, message):
    if not test:
        raise ArithmeticError(message)


# Cyclotomic reduction by the monic degree-eight polynomial, not by the
# original sqrt(5)/sqrt(10+2sqrt(5))/i multiplication table.
def zreduce(p):
    p = dict(p)
    while p and max(p) >= 8:
        k = max(p); a = p.pop(k)
        for shift, sign in ((2,1),(4,-1),(6,1),(8,-1)):
            j = k-shift
            p[j] = p.get(j,0) + sign*a
            if not p[j]: del p[j]
    return p

ZP = [zreduce({k:1}) for k in range(40)]
SP = {0:-1}
for n in (2,18):
    for k,v in ZP[n].items(): SP[k]=SP.get(k,0)+2*v
SP = {k:v for k,v in SP.items() if v}

@lru_cache(None)
def reduce_monomial(a,b):
    """Return integer coefficients in the cyclotomic/cubic basis."""
    if b < 3:
        return tuple((k+8*b,v) for k,v in zreduce({a:1}).items())
    out = {}
    # x^3=5*s*x^2+(100-20*s)*x+(500-200*s).
    for p,plain,scoef in ((b-1,0,5),(b-2,100,-20),(b-3,500,-200)):
        terms = {0:plain}
        for k,v in SP.items(): terms[k]=terms.get(k,0)+scoef*v
        for k,v in terms.items():
            if not v: continue
            for j,t in reduce_monomial(a+k,p): out[j]=out.get(j,0)+v*t
    return tuple((k,v) for k,v in out.items() if v)

MULT = [[reduce_monomial(j%8+k%8,j//8+k//8) for k in range(24)] for j in range(24)]

class C:
    __slots__ = ('v','den','nz')
    def __init__(self,v=0,den=1):
        if isinstance(v,C): self.v,self.den,self.nz=v.v,v.den,v.nz; return
        if isinstance(v,Fraction): v,den=v.numerator,v.denominator
        if isinstance(v,int): v=[v]+[0]*23
        ensure(len(v)==24 and int(den)!=0,'bad exact coefficient')
        v=list(map(int,v)); den=int(den)
        if den<0: v=[-a for a in v]; den=-den
        g=den
        for a in v: g=math.gcd(g,a)
        self.v=tuple(a//g for a in v); self.den=den//g
        self.nz=tuple((i,a) for i,a in enumerate(self.v) if a)
    def __bool__(self): return bool(self.nz)
    def __eq__(self,b):
        b=C(b); return self.v==b.v and self.den==b.den
    def __neg__(self): return C([-v for v in self.v],self.den)
    def __add__(self,b):
        b=C(b)
        if not self: return b
        if not b: return self
        g=math.gcd(self.den,b.den); p=b.den//g; q=self.den//g
        return C([a*p+c*q for a,c in zip(self.v,b.v)],self.den*p)
    __radd__=__add__
    def __sub__(self,b): return self+-C(b)
    def __rsub__(self,b): return C(b)+-self
    def __mul__(self,b):
        b=C(b)
        if not self or not b: return ZERO
        out=[0]*24
        for j,a in self.nz:
            for k,c in b.nz:
                for t,n in MULT[j][k]: out[t]+=a*c*n
        return C(out,self.den*b.den)
    __rmul__=__mul__
    def __pow__(self,n):
        ensure(isinstance(n,int) and n>=0,'only nonnegative powers required')
        result=ONE; a=self
        while n:
            if n&1: result=result*a
            a=a*a; n//=2
        return result
    def conjugate(self):
        out=[0]*24
        for j,a in self.nz:
            for k,v in reduce_monomial((-(j%8))%20,j//8): out[k]+=a*v
        return C(out,self.den)
    def rational_scale(self,n,d=1): return C([n*a for a in self.v],self.den*d)

def basis(k):
    v=[0]*24; v[k]=1; return C(v)
ZERO=C(); ONE=C(1); Z=basis(1); X=basis(8)
ZS=[Z**k for k in range(20)]
S=2*(ZS[2]+ZS[18])-1; U=2*(ZS[1]+ZS[19]); I=ZS[5]
MU=X.rational_scale(1,5)
TB=[(S**(k%2))*(X**((k//2)%3))*(U**((k//6)%2))*(I**(k//12)) for k in range(24)]


def load_scalar(o):
    ns=list(map(int,o['n'])); d=int(o['d'])
    ensure(len(ns)==24 and d>0,'malformed scalar input')
    v=[0]*24
    for n,t in zip(ns,TB):
        ensure(t.den==1,'unexpected conversion denominator')
        if n:
            for k,a in t.nz: v[k]+=n*a
    return C(v,d)

def matrix(o): return [[load_scalar(a) for a in row] for row in o]

def canon(w):
    """Independent free-product normal form, separating Alice and Bob."""
    parties=[[],[]]
    for r,k in w:
        ensure(r in range(4),'unknown generator')
        k %= 5
        if not k: continue
        a=parties[r&1]
        if a and a[-1][0]==r:
            k=(a.pop()[1]+k)%5
        if k: a.append((r,k))
    return tuple(parties[0]+parties[1])

def star(w): return canon(tuple((r,5-k) for r,k in reversed(w)))
def word_product(a,b): return canon(a+b)


def read_interval(o):
    def f(q): return Fraction(int(q['numerator']),int(q['denominator']))
    a,b=f(o['lower']),f(o['upper']); ensure(a<=b,'reversed interval'); return a,b

def isum(a,b): return a[0]+b[0],a[1]+b[1]
def imul(a,b):
    vals=[a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]]
    return min(vals),max(vals)
def iscale(a,c):
    vals=[a[0]*c,a[1]*c]; return min(vals),max(vals)

def complex_imul(a,b):
    return (isum(imul(a[0],b[0]),iscale(imul(a[1],b[1]),-1)),
            isum(imul(a[0],b[1]),imul(a[1],b[0])))

def p(t): return 5*t**6-65*t**4+144*t*t+96*t+16

def interval_basis(box):
    m=read_interval(box['mu']); s=read_interval(box['sqrt5']); u=read_interval(box['u'])
    ensure(m[0]>3 and p(m[0])<0<p(m[1]),'mu not isolated on largest-root branch')
    ensure(0<s[0] and s[0]**2<5<s[1]**2,'sqrt5 branch not enclosed')
    ensure(0<u[0] and u[0]**2<10+2*s[0] and u[1]**2>10+2*s[1], 'u branch not enclosed')
    zr=iscale(u,Fraction(1,4)); zi=iscale(isum(s,(Fraction(-1),Fraction(-1))),Fraction(1,4))
    zp=[((Fraction(1),Fraction(1)),(Fraction(0),Fraction(0)))]
    for _ in range(7): zp.append(complex_imul(zp[-1],(zr,zi)))
    xb=[(Fraction(1),Fraction(1)),iscale(m,5),imul(iscale(m,5),iscale(m,5))]
    return [(imul(zp[a][0],xb[b]),imul(zp[a][1],xb[b])) for b in range(3) for a in range(8)]

def bounds(c,ib):
    re=(Fraction(0),Fraction(0)); im=re
    for k,n in c.nz:
        q=Fraction(n,c.den)
        re=isum(re,iscale(ib[k][0],q)); im=isum(im,iscale(ib[k][1],q))
    return re,im

def positive(c,ib,what):
    ensure(c.conjugate()==c,what+' not exactly real')
    re,im=bounds(c,ib)
    ensure(re[0]>0 and im[0]<=0<=im[1],what+' not certified positive')
    return re


def make_bell():
    # Direct discrete Fourier transform of f(z)=1-z/2, not the discovery
    # formula 1/[2(1-omega^{-k})].  This avoids all algebraic inversions.
    ck=[]
    for k in range(5):
        ck.append(sum(ZS[(-4*k*r)%20].rational_scale(2-r,10) for r in range(5)))
    ensure(not ck[0],'nonzero constant Fourier coefficient')
    for r in range(5):
        ensure(sum(ck[k]*ZS[(4*k*r)%20] for k in range(5))==C(Fraction(2-r,2)), 'Fourier synthesis mismatch')
    out={}
    for r in range(4):
        for k in range(1,5):
            w=canon(((r,k),((r+1)%4,5-k)))
            val=ck[k]*(ZS[-4*k%20] if r==3 else ONE)
            out[w]=out.get(w,ZERO)+val
    return out


def verify_words(kernels,cert):
    alice=[()]+[((r,k),) for r in (0,2) for k in range(1,5)]
    bob=[()]+[((r,k),) for r in (1,3) for k in range(1,5)]
    q=[a+b for a in alice for b in bob]
    given=[tuple(map(tuple,w)) for w in kernels['Q']]
    ensure(q==given,'81-word basis does not match the declared physical algebra')
    allwords={word_product(star(a),b) for a in q for b in q}
    ensure(len(allwords)==1681,'unexpected full word universe')
    lhs={w:ZERO for w in allwords}
    size=0
    ensure(cert['blocks']==[1,6,7,8,9],'unexpected certificate block set')
    for k in cert['blocks']:
        E=matrix(kernels['kernels'][str(k)]['E']); H=matrix(cert['H'][str(k)])
        n=len(H); size+=n
        ensure(len(E)==81 and all(len(row)==n for row in E),'bad E dimensions')
        ensure(all(len(row)==n for row in H),'bad H dimensions')
        ensure(all(H[a][b]==H[b][a].conjugate() for a in range(n) for b in range(n)), 'non-Hermitian H')
        nz=[j for j in range(81) if any(E[j])]
        EH={i:[sum(E[i][a]*H[a][b] for a in range(n)) for b in range(n)] for i in nz}
        for i in nz:
            for j in nz:
                x=sum(EH[i][b]*E[j][b].conjugate() for b in range(n))
                w=word_product(star(q[i]),q[j])
                lhs[w]=lhs[w]+x
                # J * conjugate(E H E*) * J, with q_{J(i)}=q_i^*.
                wp=word_product(q[i],star(q[j]))
                lhs[wp]=lhs[wp]+x.conjugate()
    rhs={w:-a for w,a in make_bell().items()}; rhs[()]=MU
    bad=[w for w in allwords if lhs[w]!=rhs.get(w,ZERO)]
    ensure(not bad,'nonzero exact Bell SOS word residual: '+str(bad[:3]))
    return {'operator_basis':len(q),'full_word_coefficients_exactly_checked':len(allwords),'positive_block_total_size':size,'all_coefficients_identically_zero':True}


def verify_positive(cert,proof):
    ib=interval_basis(proof['embedding_boxes']); all_lower=[]; block_info={}
    for k in cert['blocks']:
        H=matrix(cert['H'][str(k)]); b=proof['blocks'][str(k)]
        L=matrix(b['L']); D=list(map(load_scalar,b['D'])); n=len(H)
        ensure(len(L)==n and len(D)==n and all(len(row)==n for row in L),'bad LDL dimensions')
        ensure(all(L[i][j]==(1 if i==j else 0) for i in range(n) for j in range(i,n)), 'L not unit lower triangular')
        for i,j in product(range(n),repeat=2):
            ensure(H[i][j]==sum(L[i][r]*D[r]*L[j][r].conjugate() for r in range(n)), 'LDL reconstruction failed')
        bs=[positive(d,ib,f'block{k} pivot{j}') for j,d in enumerate(D)]
        all_lower.extend(a for a,b in bs)
        block_info[str(k)]={'dimension':n,'exact_LDL':True,'strict_positive_pivots':len(bs)}
    return {'blocks':block_info,'pivots_certified':len(all_lower),'minimum_rational_lower_bound':str(min(all_lower))},ib


def step(r,j):
    # Direct monomial implementation of the specified standard Fourier
    # projectors.  All phase exponents are integers modulo twenty.
    if r==0: return (j-1)%5,0
    if r==1: return (j+1)%5,(16 if j==4 else 1)
    if r==2: return (j-1)%5,(12 if j==0 else 2)
    if r==3: return (j+1)%5,(8 if j==4 else 3)
    raise ValueError(r)

def act(w,a,b):
    e=0
    for r,k in reversed(w):
        for _ in range(k%5):
            if r&1: b,t=step(r,b)
            else: a,t=step(r,a)
            e+=t
    return a,b,ZS[e%20]


def verify_physical(kernels,ib):
    gamma=list(map(load_scalar,kernels['gamma']))
    ensure(len(gamma)==5,'wrong Schmidt vector length')
    for j,g in enumerate(gamma): positive(g,ib,f'gamma{j}')
    norm=sum(g.conjugate()*g for g in gamma); positive(norm,ib,'state norm')
    # Independently construct every eigenprojector using Fourier vectors and
    # verify U=Sum omega^outcome P_outcome entrywise. Normalization is 1/5.
    spectral_entries=0
    for r in range(4):
        for j,l in product(range(5),repeat=2):
            val=ZERO
            for a in range(5):
                if r%2==0:
                    phase=4*(j-l)*a+(0 if r==0 else 2*(j-l))
                else:
                    phase=-4*(j-l)*a+(1 if r==1 else -1)*(j-l)
                label=a+(1 if r>=2 else 0)
                val+=ZS[(phase+4*label)%20].rational_scale(1,5)
            dst,e=step(r,l)
            ensure(val==(ZS[e] if dst==j else ZERO),'Fourier-projector/unitary bridge failed')
            spectral_entries+=1
        perm=[]
        for j in range(5):
            dst,e=step(r,j); perm.append(dst)
            ensure(ZS[e].conjugate()*ZS[e]==ONE,'unitarity phase failed')
            t=j; acc=0
            for _ in range(5): t,ee=step(r,t); acc+=ee
            ensure(t==j and ZS[acc%20]==ONE,'fifth-order unitary relation failed')
        ensure(sorted(perm)==list(range(5)),'non-unitary basis permutation')
    out=[ZERO]*25
    for w,c in make_bell().items():
        for j,g in enumerate(gamma):
            a,b,e=act(w,j,j); out[5*a+b]+=c*g*e
    for a,b in product(range(5),repeat=2):
        ensure(out[5*a+b]==(MU*gamma[a] if a==b else ZERO),'full 25-coordinate Bell eigenvector failure')
    # Check conventional probability CGLMP against the relabelled cyclic
    # expression for every deterministic assignment. Equality of the four
    # pairwise coefficients is also verified separately below.
    worst=Fraction(-100); tests=0
    for a0,b0,a1,b1 in product(range(5),repeat=4):
        cyclic=sum(Fraction(2-r,2) for r in ((a0-b0)%5,(b0-a1-1)%5,(a1-b1)%5,(b1-a0)%5))
        standard=Fraction(0)
        for k in range(2):
            w=Fraction(2-k,2)
            pos=((a0-b0)%5==k)+((b0-a1)%5==(k+1)%5)+((a1-b1)%5==k)+((b1-a0)%5==k)
            neg=((a0-b0)%5==(-k-1)%5)+((b0-a1)%5==(-k)%5)+((a1-b1)%5==(-k-1)%5)+((b1-a0)%5==(-k-1)%5)
            standard+=w*(pos-neg)
        ensure(cyclic==standard,'CGLMP outcome relabelling mismatch')
        worst=max(worst,cyclic); tests+=1
    ensure(worst==2,'incorrect local normalization')
    # For each of the four setting pairs, all 25 event coefficients.
    for edge in range(4):
        for a,b in product(range(5),repeat=2):
            shift=1 if edge==1 else 0
            direct=Fraction(2-((a-b-shift)%5),2)
            conventional=Fraction(0)
            for k in range(2):
                v=Fraction(2-k,2)
                conventional+=v*(int((a-b)%5==(k+shift)%5)-int((a-b)%5==(-k-1+shift)%5))
            ensure(direct==conventional,'pairwise event coefficient mismatch')
    return {'full_Bell_eigenvector_coordinates':25,'projector_to_unitary_entries':spectral_entries,'deterministic_normalization_tests':tests,'pairwise_probability_coefficients':100,'local_bound':2,'dimension_for_attainment':[5,5],'state_positive_and_normalizable':True}


def verify(root,physical=True,quiet=False):
    st=time.monotonic()
    data=json.loads((root/'EXACT_KERNELS.json').read_text())
    cert=json.loads((root/'EXACT_SOS_CANDIDATE.json').read_text())
    proof=json.loads((root/'POSITIVITY_CERTIFICATE.json').read_text())
    ensure(ZS[10]==-1 and ZS[5]*ZS[5]==-1 and Z**20==1,'cyclotomic embedding identities')
    ensure(S*S==5 and U*U==10+2*S and 4*Z==U+I*(S-1),'tower conversion fails')
    ensure(5*MU**6-65*MU**4+144*MU**2+96*MU+16==0,'target polynomial not implied')
    wordinfo=verify_words(data,cert)
    if not quiet: print('Independent cyclotomic normal-form SOS check: PASS',wordinfo,flush=True)
    posinfo,ib=verify_positive(cert,proof)
    if not quiet: print('Independent LDL and rational interval check: PASS; pivots',posinfo['pivots_certified'],flush=True)
    phinfo=verify_physical(data,ib) if physical else {'status':'SKIPPED BY EXPLICIT CHECKER OPTION'}
    if not quiet: print('Independent physical lower bound and convention check:', 'PASS' if physical else 'SKIPPED',flush=True)
    return {'status':'PASS' if physical else 'UPPER_BOUND_ONLY_PASS','checker':'independent cyclotomic-basis standard-library implementation; same author/agent, not an external audit','word_check':wordinfo,'positivity':posinfo,'physical':phinfo,'elapsed_seconds':time.monotonic()-st}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--skip-physical',action='store_true')
    args=parser.parse_args()
    result=verify(args.root,not args.skip_physical)
    if args.output: args.output.write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
