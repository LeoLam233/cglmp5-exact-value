#!/usr/bin/env python3
"""Independent exact adversarial audit of the supplied CGLMP5 certificate.

Python >=3.10, standard library only (mpmath is optional for display).
Usage: python audit.py /path/to/CGLMP5_WEB6PRO_ADVERSARIAL_AUDIT_PACK_v2
No candidate verifier, multiplication table, or pass flag is used.
Exact field representation: Q[z,x]/(Phi_20(z), x^3-5s*x^2-(100-20s)*x-500+200s),
where s=2(z^2+z^-2)-1. Elements have 24 integer coefficients and one positive denominator.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, math, os, sys, time
from collections import defaultdict, Counter
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

T0=time.perf_counter()
RESULTS={"arithmetic":"exact integer/common-denominator cyclotomic-cubic quotient ring", "checks":{}}
def note(name, result):
    RESULTS['checks'][name]=result
    print(f'[{time.perf_counter()-T0:.2f}s] {name}: {json.dumps(result,ensure_ascii=False)}',flush=True)
def require(test, msg):
    if not test: raise AssertionError(msg)

def cr(v):
    """Reduce an integer polynomial modulo z^8-z^6+z^4-z^2+1."""
    v=list(v)+[0]*max(0,8-len(v))
    for k in range(len(v)-1,7,-1):
        c=v[k]
        if c:
            v[k-2]+=c; v[k-4]-=c; v[k-6]+=c; v[k-8]-=c
    return tuple(v[:8])
def ca(a,b): return tuple(x+y for x,y in zip(a,b))
def cs(a,n): return tuple(x*n for x in a)
def cm(a,b):
    v=[0]*15
    for j,x in enumerate(a):
        if x:
            for k,y in enumerate(b):
                if y: v[j+k]+=x*y
    return cr(v)
CZ=(0,)*8
CO=(1,)+(0,)*7
ZPOW=[CO]
for _ in range(1,40): ZPOW.append(cr((0,)+ZPOW[-1]))
require(ZPOW[20]==CO and ZPOW[10]==cs(CO,-1),'Cyclotomic root order')
S=ca(cs(ca(ZPOW[2],ZPOW[18]),2),cs(CO,-1))
U=cs(ca(ZPOW[1],ZPOW[19]),2)
I=ZPOW[5]
CUBIC=[ca(cs(CO,500),cs(S,-200)),ca(cs(CO,100),cs(S,-20)),cs(S,5)]
XRED=[]
for b in range(5):
    p=[CZ]*5; p[b]=CO
    for k in range(4,2,-1):
        for j in range(3): p[k-3+j]=ca(p[k-3+j],cm(p[k],CUBIC[j]))
        p[k]=CZ
    XRED.append(p[:3])
RED=[]
for b in range(5):
    for a in range(15):
        v=tuple(t for j in range(3) for t in cm(XRED[b][j],ZPOW[a]))
        RED.append(tuple((i,c) for i,c in enumerate(v) if c))
CONJ=tuple(ZPOW[(-a)%20] for a in range(8))

class E:
    __slots__=('n','d','nz')
    def __init__(self,n=(),d=1):
        n=tuple(n) if n else (0,)*24
        require(len(n)==24 and isinstance(d,int) and d!=0,'Invalid field element')
        if d<0: n=tuple(-a for a in n); d=-d
        g=d
        for a in n:
            g=math.gcd(g,a)
            if g==1: break
        if g!=1: n=tuple(a//g for a in n); d//=g
        self.n=n; self.d=d
        self.nz=tuple((j//8,j%8,a) for j,a in enumerate(n) if a)
    @staticmethod
    def rat(n,d=1): return E((n,)+(0,)*23,d)
    @staticmethod
    def cyc(c,d=1,b=0): return E((0,)*(8*b)+tuple(c)+(0,)*(16-8*b),d)
    def __bool__(self): return bool(self.nz)
    def __eq__(self,o):
        if isinstance(o,int): o=E.rat(o)
        return isinstance(o,E) and self.d==o.d and self.n==o.n
    def __hash__(self): return hash((self.n,self.d))
    def __neg__(self): return E(tuple(-a for a in self.n),self.d)
    def __add__(self,o):
        if isinstance(o,int): o=E.rat(o)
        if not self: return o
        if not o: return self
        g=math.gcd(self.d,o.d); da=o.d//g; db=self.d//g
        return E(tuple(a*da+b*db for a,b in zip(self.n,o.n)),self.d*da)
    __radd__=__add__
    def __sub__(self,o): return self+-o
    def __rsub__(self,o): return -self+o
    def __mul__(self,o):
        if isinstance(o,int): return E(tuple(a*o for a in self.n),self.d)
        if not self or not o: return ZERO
        if len(self.nz)==1 and self.nz[0][:2]==(0,0): return E(tuple(self.n[0]*a for a in o.n),self.d*o.d)
        if len(o.nz)==1 and o.nz[0][:2]==(0,0): return E(tuple(o.n[0]*a for a in self.n),self.d*o.d)
        raw=[0]*75
        for b,a,v in self.nz:
            for f,e,w in o.nz: raw[15*(b+f)+a+e]+=v*w
        out=[0]*24
        for j,v in enumerate(raw):
            if v:
                for k,c in RED[j]: out[k]+=v*c
        return E(out,self.d*o.d)
    __rmul__=__mul__
    def __truediv__(self,o):
        # Division is permitted only by a nonzero rational integer.
        require(isinstance(o,int) and o!=0,'Only verified rational division is allowed')
        return E(self.n,self.d*o)
    def __pow__(self,n):
        require(isinstance(n,int) and n>=0,'Only nonnegative powers')
        a=self; ans=ONE
        while n:
            if n&1: ans=ans*a
            a=a*a; n//=2
        return ans
    def conj(self):
        out=[0]*24
        for b,a,v in self.nz:
            for j,c in enumerate(CONJ[a]): out[b*8+j]+=v*c
        return E(out,self.d)
    def serial(self): return {'n':[str(a) for a in self.n],'d':str(self.d)}

ZERO=E(); ONE=E.rat(1); z=E.cyc(ZPOW[1]); s=E.cyc(S); u=E.cyc(U); ii=E.cyc(I); x=E.cyc(CO,b=1); mu=x/5
TOWER=[]
for j in range(24):
    a=j%2; b=(j//2)%3; c=(j//6)%2; e=j//12
    TOWER.append((s**a)*(x**b)*(u**c)*(ii**e))
require(all(v.d==1 for v in TOWER),'Tower conversion must be integral')
@lru_cache(None)
def decode_cached(ns,ds):
    require(len(ns)==24 and ds>0,'Scalar encoding requires 24 integers and positive denominator')
    out=[0]*24
    for v,t in zip(ns,TOWER):
        if v:
            for j,c in enumerate(t.n): out[j]+=v*c
    return E(out,ds)
def decode(o): return decode_cached(tuple(int(a) for a in o['n']),int(o['d']))

def word(raw):
    """Independent normal form: pair of reduced free-product words, one per party."""
    parties=[[],[]]
    for rr,kk in raw:
        r=int(rr); k=int(kk)%5
        require(0<=r<4,'Unrecognized generator')
        if not k: continue
        p=parties[r%2]
        if p and p[-1][0]==r:
            k=(k+p.pop()[1])%5
            if k: p.append((r,k))
        else: p.append((r,k))
    return tuple(map(tuple,parties))
ID=((),())
def flatten(w): return w[0]+w[1]
def wm(v,w): return word(flatten(v)+flatten(w))
def wa(w): return word([(r,-k) for r,k in reversed(flatten(w))])
def padd(p,w,c):
    p[w]=p.get(w,ZERO)+c

def frac(o): return F(int(o['numerator']),int(o['denominator']))
def interval(o): return (frac(o['lower']),frac(o['upper']))
def ia(a,b): return (a[0]+b[0],a[1]+b[1])
def im(a,b):
    q=(a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]); return min(q),max(q)
def isc(a,n): return im(a,(F(n),F(n)))
def ip(a,n):
    v=(F(1),F(1))
    for _ in range(n): v=im(v,a)
    return v

def pv(t): return 5*t**6-65*t**4+144*t**2+96*t+16

def event2(ax,by,a,b):
    """Twice the coefficient from the ORIGINAL eight signed event types, not f()."""
    v=0
    for k in (0,1):
        weight=2-k
        if (ax,by)==(0,0):
            v+=weight*(int((a-b-k)%5==0)-int((a-b+k+1)%5==0))
        elif (ax,by)==(1,0):
            v+=weight*(int((b-a-k-1)%5==0)-int((b-a+k)%5==0))
        elif (ax,by)==(1,1):
            v+=weight*(int((a-b-k)%5==0)-int((a-b+k+1)%5==0))
        elif (ax,by)==(0,1):
            v+=weight*(int((b-a-k)%5==0)-int((b-a+k+1)%5==0))
        else: raise AssertionError('Setting')
    return v

def basic(root,data):
    manifest={}
    for ln in (root/'SHA256SUMS.txt').read_text().splitlines():
        h,n=ln.split(); actual=hashlib.sha256((root/n).read_bytes()).hexdigest()
        require(h==actual,f'hash mismatch {n}'); manifest[n]=actual
    note('input_sha256',manifest)
    require(s*s==5 and u*u==10+2*s and ii*ii==-1,'Actual embedding relations')
    require((u+ii*(s-1))/4==z and z**5==ii and z**20==1,'z branch identities')
    require(mu**3==s*mu**2+(4-(s*4)/5)*mu+4-(s*8)/5,'Cubic reduction')
    require(pv(mu)==0,'Sextic reduction')
    # Polynomial identity A(t)^2-5B(t)^2=5p(t), using independent integer convolution.
    def pm(a,b):
        c=[0]*(len(a)+len(b)-1)
        for i,v in enumerate(a):
            for j,w in enumerate(b): c[i+j]+=v*w
        return c
    aa=pm([-20,-20,0,5],[-20,-20,0,5]); bb=pm([-8,-4,5],[-8,-4,5])+[0,0]
    require([v-5*w for v,w in zip(aa,bb)]==[80,480,720,0,-325,0,25],'A^2-5B^2=5p')
    require(pv(F(3))==-20 and pv(F(31,10))>0,'Coarse isolation')
    boxes={k:interval(v) for k,v in data['sos']['embedding_boxes'].items()}
    mlo,mhi=boxes['mu']; slo,shi=boxes['sqrt5']; ulo,uhi=boxes['u']
    require(3<mlo<mhi<F(31,10) and pv(mlo)<0<pv(mhi),'mu rational isolation')
    require(0<slo<shi and slo*slo<5<shi*shi,'sqrt5 branch')
    require(0<ulo<uhi and ulo*ulo<10+2*slo and uhi*uhi>10+2*shi,'u robust branch enclosure')
    require(slo>1 and ulo*ulo>8,'z first-sector selection')
    note('root_and_embedding',{'sextic_identity':True,'cubic_branch':'+sqrt(5)', 'positive_root_boxes':True,'mu_interval_width':str(mhi-mlo),'sqrt5_interval_width':str(shi-slo),'u_interval_width':str(uhi-ulo),'largest_root_argument':'For t>=3: 30t^2-260>=10, so p\u2032(t)>0.'})
    # Every single setting/outcome coefficient must match, not just a restricted strategy.
    events=0
    for ax,by,a,b in itertools.product(range(2),range(2),range(5),range(5)):
        delta={(0,0):a-b,(1,0):b-a-1,(1,1):a-b,(0,1):b-a}[(ax,by)]
        require(event2(ax,by,a,b)==2-(delta%5),'Event convention mismatch');events+=1
    classical=[]
    for a0,a1,b0,b1 in itertools.product(range(5),repeat=4):
        score=sum(event2(ax,by,[a0,a1][ax],[b0,b1][by]) for ax,by in itertools.product(range(2),repeat=2))
        residue=(a0-b0)%5+(b0-a1-1)%5+(a1-b1)%5+(b1-a0)%5
        require(score==8-residue and residue%5==4,'Deterministic cycle mismatch')
        classical.append(score)
    require(max(classical)==4,'Classical bound')
    coeff=[]
    for k in range(5):
        c=sum((E.cyc(ZPOW[(-4*k*t)%20])*(2-t) for t in range(5)),ZERO)/10
        coeff.append(c)
    require(coeff[0]==0,'DFT constant')
    for k in range(1,5):
        require(2*(ONE-z**((20-4*k)%20))*coeff[k]==ONE,'DFT inverse formula')
        require(coeff[k].conj()==coeff[5-k],'DFT conjugation')
    for t in range(5): require(sum((coeff[k]*z**((4*k*t)%20) for k in range(5)),ZERO)==E.rat(2-t,2),'DFT reconstruction')
    B={}
    for r in range(3):
        for k in range(1,5): padd(B,word([(r,k),(r+1,-k)]),coeff[k])
    for k in range(1,5): padd(B,word([(3,k),(0,-k)]),coeff[k]*z**((20-4*k)%20))
    require(all(B.get(wa(w),ZERO)==c.conj() for w,c in B.items()),'Bell Hermitian')
    note('events_and_fourier',{'single_event_coefficients_checked':events,'deterministic_assignments':625,'local_bound':2,'DFT_exact':True,'Bell_nonzero_words':len(B),'Bell_hermitian':True})
    # Normal-form stress tests against group inverse and associativity; no same-party commutation.
    require(word([(0,1),(2,1)])!=word([(2,1),(0,1)]),'Same-party generators erroneously commute')
    require(word([(0,1),(1,1)])==word([(1,1),(0,1)]),'Cross-party commutation')
    Q=[word(flatten(a)+flatten(b)) for a in [ID]+[word([(r,k)]) for r in [0,2] for k in range(1,5)] for b in [ID]+[word([(r,k)]) for r in [1,3] for k in range(1,5)]]
    require(len(Q)==81 and len(set(Q))==81,'Q construction')
    require(Q==[word(w) for w in data['kernels']['Q']],'Serialized Q mismatch')
    universe={wm(wa(v),w) for v in Q for w in Q}
    require(len(universe)==1681,'Q*Q universe count')
    require(universe=={word(w) for w in data['kernels']['words']},'Serialized universe mismatch')
    for a in Q:
        require(wm(a,wa(a))==ID and wa(wa(a))==a,'Word inverse')
    note('word_algebra',{'representation':'two independent C5*C5 normal words, one for each party','same_party_noncommutation_preserved':True,'Q_size':81,'full_Gram_word_universe':1681})
    return boxes,B,Q,universe


def positivity(data,boxes):
    sb=boxes['sqrt5']; xb=isc(boxes['mu'],5); ub=boxes['u']
    weights=[]; bounds=[]
    for t in data['sos']['terms']:
        d=decode(t['weight']); require(d==d.conj(),f"Non-real weight {t['id']}")
        # Serialized real tower basis, evaluated with strict rational interval arithmetic.
        n=list(map(int,t['weight']['n'])); den=int(t['weight']['d'])
        require(all(a==0 for a in n[12:]),'Weight needs more general real extraction')
        v=(F(0),F(0))
        for j,c in enumerate(n[:12]):
            a=j%2; b=(j//2)%3; e=j//6
            v=ia(v,isc(im(im(ip(sb,a),ip(xb,b)),ip(ub,e)),F(c,den)))
        require(v[0]>0,f"Weight not proved positive: {t['id']}")
        weights.append(d); bounds.append(v)
    note('positive_SOS_weights',{'count':len(weights),'all_exactly_real':True,'all_rational_lower_bounds_positive':True,'lower_bound_displays':{t['id']:format(float(v[0]),'.17g') for t,v in zip(data['sos']['terms'],bounds)},'minimum_lower_bound_exact':str(min(v[0] for v in bounds))})
    return weights,bounds


def sos_identity(data,B,Q,weights):
    expected={w:-c for w,c in B.items()}; expected[ID]=mu
    summed={}; polys=[]; rawproducts=0
    for t,d in zip(data['sos']['terms'],weights):
        R={}
        for item in t['polynomial']:
            w=word(item['word']); c=decode(item['coefficient'])
            require(w in Q,'R word outside Q')
            require(c!=ZERO,'Explicit zero R coefficient')
            require(w not in R,'Repeated polynomial word')
            R[w]=c
        polys.append(R)
        # Form R* R and R R* separately; do not infer one through symmetry.
        for a,ca_ in R.items():
            for b,cb_ in R.items():
                cc=d*ca_.conj()*cb_
                padd(summed,wm(wa(a),b),cc)
                padd(summed,wm(b,wa(a)),cc)
                rawproducts+=2
        print(f"[{time.perf_counter()-T0:.2f}s] expanded SOS term {t['id']}",flush=True)
    touched=set(summed)|set(expected)
    wrong=[w for w in touched if summed.get(w,ZERO)!=expected.get(w,ZERO)]
    require(not wrong,f'Nonzero exact SOS residual in {len(wrong)} words: {wrong[:3]}')
    note('SOS_identity',{'terms':len(polys),'explicit_nonzero_scalar_coefficients':sum(map(len,polys)),'raw_ordered_products':rawproducts,'word_positions_checked':len(touched),'nonzero_residual_words':len(wrong),'nonzero_output_words':sum(bool(v) for v in summed.values()),'identity':'mu I-B=sum_j d_j(R_j^*R_j+R_jR_j^*)'})
    return polys,summed


def mm(A,B):
    rows=len(A); inner=len(B); cols=len(B[0]); C=[[ZERO for _ in range(cols)] for _ in range(rows)]
    for r in range(rows):
        for k in range(inner):
            if A[r][k]:
                for c in range(cols):
                    if B[k][c]: C[r][c]=C[r][c]+A[r][k]*B[k][c]
    return C

def adj(A): return [[A[j][i].conj() for j in range(len(A))] for i in range(len(A[0]))]
def eye(n): return [[ONE if i==j else ZERO for j in range(n)] for i in range(n)]
def msum(matrices,n):
    C=[[ZERO for _ in range(n)] for _ in range(n)]
    for M in matrices:
        for i in range(n):
            for j in range(n): C[i][j]=C[i][j]+M[i][j]
    return C

def real_tower_interval(encoded,boxes):
    require(all(int(v)==0 for v in encoded['n'][12:]),'Real tower interval expects no i component')
    v=(F(0),F(0)); ds=int(encoded['d'])
    for j,raw in enumerate(encoded['n'][:12]):
        c=int(raw)
        if c:
            a=j%2; b=(j//2)%3; e=j//6
            v=ia(v,isc(im(im(ip(boxes['sqrt5'],a),ip(isc(boxes['mu'],5),b)),ip(boxes['u'],e)),F(c,ds)))
    return v

def complex_interval_mul(a,b):
    return (ia(im(a[0],b[0]),isc(im(a[1],b[1]),-1)),ia(im(a[0],b[1]),im(a[1],b[0])))

def cyclotomic_interval(v,boxes):
    zero=(F(0),F(0)); one=(F(1),F(1))
    zz=(isc(boxes['u'],F(1,4)),isc(ia(boxes['sqrt5'],(F(-1),F(-1))),F(1,4)))
    zp=[(one,zero)]
    for j in range(7): zp.append(complex_interval_mul(zp[-1],zz))
    out=(zero,zero)
    for b,a,c in v.nz:
        power=ip(isc(boxes['mu'],5),b)
        re=isc(im(zp[a][0],power),F(c,v.d)); imag=isc(im(zp[a][1],power),F(c,v.d))
        out=(ia(out[0],re),ia(out[1],imag))
    return out


def extended(data,boxes,B,Q,weights,bounds,polys,summed):
    # A second positivity path, AFTER conversion to cyclotomic-cubic coordinates.
    independent_bounds=[]
    for t,d in zip(data['sos']['terms'],weights):
        rb,ib=cyclotomic_interval(d,boxes)
        require(rb[0]>0 and ib[0]<=0<=ib[1],f"Cyclotomic rectangle positivity failed for {t['id']}")
        independent_bounds.append(rb)
    note('independent_cyclotomic_positivity',{'all_14_real_lower_bounds_positive':True,'minimum_lower_bound_display':format(float(min(v[0] for v in independent_bounds)),'.17g'),'minimum_lower_bound_exact':str(min(v[0] for v in independent_bounds))})

    # Reconstruct the SMALL Hermitian blocks, LDL*, phase embeddings, and the full Gram expansion.
    qindex={w:i for i,w in enumerate(Q)}; G={}; Eblocks={}; hentries=0; lentries=0; eentries=0; Rentries=0
    for key in map(str,data['candidate']['blocks']):
        kd=data['kernels']['kernels'][key]; pd=data['positivity']['blocks'][key]
        H=[[decode(c) for c in row] for row in data['candidate']['H'][key]]
        L=[[decode(c) for c in row] for row in pd['L']]
        D=[decode(c) for c in pd['D']]; n=len(D)
        require(len(H)==len(L)==n and all(len(row)==n for row in H+L),'Gram block shapes')
        require(H==adj(H),'H not Hermitian')
        for i in range(n):
            for j in range(n):
                require((i!=j or L[i][j]==ONE) and (i>=j or L[i][j]==ZERO),'L not unit lower triangular');lentries+=1
                rebuilt=sum((L[i][k]*D[k]*L[j][k].conj() for k in range(n)),ZERO)
                require(H[i][j]==rebuilt,f'LDL failure {key}/{i}/{j}'); hentries+=1
        for j in range(n):
            pos=next(i for i,t in enumerate(data['sos']['terms']) if t['id']==key+':'+str(j))
            require(D[j]==weights[pos],'LDL/SOS pivot mismatch')
            require(interval(pd['pivot_enclosures'][j])==bounds[pos],'Published pivot enclosure mismatch')
        Eb=[[decode(c) for c in row] for row in kd['E']]
        K=[[decode(c) for c in row] for row in kd['K']]
        exps=kd['exponents']
        require(len(Eb)==81 and all(len(row)==n for row in Eb),'E shape')
        for wi in range(81):
            for j in range(n):
                # Build phase matrix from exponents rather than trust the serialized E.
                rebuilt=sum((E.cyc(ZPOW[int(exps[h][wi])%20])*K[h][j] for h in range(len(K)) if exps[h][wi] is not None),ZERO)
                require(Eb[wi][j]==rebuilt,f'Phase/K/E inconsistency {key}/{wi}/{j}');eentries+=1
                rpoly=polys[next(i for i,t in enumerate(data['sos']['terms']) if t['id']==key+':'+str(j))]
                rcoef=sum((Eb[wi][h]*L[h][j] for h in range(n)),ZERO).conj()
                require(rpoly.get(Q[wi],ZERO)==rcoef,f'R != conjugate(E L), {key}/{wi}/{j}');Rentries+=1
        Eblocks[key]=Eb
        support=[i for i,row in enumerate(Eb) if any(row)]
        EH=[[sum((Eb[i][k]*H[k][j] for k in range(n)),ZERO) for j in range(n)] for i in support]
        for pi,i in enumerate(support):
            for j in support:
                c=sum((EH[pi][k]*Eb[j][k].conj() for k in range(n)),ZERO)
                G[i,j]=G.get((i,j),ZERO)+c
    require(all(c==G.get((j,i),ZERO).conj() for (i,j),c in G.items()),'Embedded Gram not Hermitian')
    gs={}
    for (i,j),c in G.items():
        padd(gs,wm(wa(Q[i]),Q[j]),c)
        padd(gs,wm(Q[j],wa(Q[i])),c)
    universe={wm(wa(v),w) for v in Q for w in Q}
    require(set(gs)<=universe,'Gram produced unexpected word')
    expected={w:-c for w,c in B.items()}; expected[ID]=mu
    for w in universe:
        require(gs.get(w,ZERO)==expected.get(w,ZERO),f'Full Gram nonzero residual {w}')
    note('Gram_LDL_and_embeddings',{'block_dimensions':[2,4,3,3,2],'Hermitian_and_LDL_entries_verified':hentries,'unit_lower_triangular_entries_verified':lentries,'phase_K_E_entries_verified':eentries,'R_equals_conjugate_EL_entries_verified':Rentries,'embedded_Gram_positions':len(G),'full_word_universe_verified':len(universe),'exact_residual_words':0,'all_published_pivot_enclosures_recomputed':True})

    # Original Fourier projectors, reconstructed without using the asserted Toeplitz matrix.
    proj={}
    for party in ('A','B'):
        for setting in range(2):
            for outcome in range(5):
                phase=(4*outcome+2*setting) if party=='A' else (-4*outcome+(1 if setting==0 else -1))
                P=[[E.cyc(ZPOW[(phase*(j-k))%20])/5 for k in range(5)] for j in range(5)]
                require(P==adj(P),'Projector Hermitian')
                proj[party,setting,outcome]=P
    orthogonality_products=0
    for party,setting in itertools.product(('A','B'),range(2)):
        ps=[proj[party,setting,a] for a in range(5)]
        require(msum(ps,5)==eye(5),'PVM completeness')
        for a,b in itertools.product(range(5),repeat=2):
            require(mm(ps[a],ps[b])==(ps[a] if a==b else [[ZERO]*5 for _ in range(5)]),'PVM orthogonality');orthogonality_products+=1
    Us=[]; Upow={}
    for r in range(4):
        party='A' if r%2==0 else 'B'; setting=r//2; shift=setting
        ur=[[sum((E.cyc(ZPOW[(4*(a+shift))%20])*proj[party,setting,a][j][k] for a in range(5)),ZERO) for k in range(5)] for j in range(5)]
        require(mm(adj(ur),ur)==eye(5),'Spectral U unitarity')
        power=eye(5);Upow[r,0]=power
        for exp in range(1,6):
            power=mm(power,ur);Upow[r,exp%5]=power
        require(power==eye(5),'U fifth power')
        Us.append(ur)
    # Exact monomial actions, extracted from reconstructed matrices rather than assumed shifts.
    mono={}
    for (r,k),M in Upow.items():
        mp=[]
        for col in range(5):
            nz=[(row,M[row][col]) for row in range(5) if M[row][col]]
            require(len(nz)==1 and nz[0][1]*nz[0][1].conj()==ONE,'Local U power not unit-modulus monomial')
            mp.append(nz[0])
        mono[r,k]=mp
    @lru_cache(None)
    def wmap(w):
        out=[]
        for col in range(25):
            a,b=divmod(col,5); phase=ONE
            for r,k in reversed(w[0]):
                a,c=mono[r,k][a];phase=phase*c
            for r,k in reversed(w[1]):
                b,c=mono[r,k][b];phase=phase*c
            out.append((5*a+b,phase))
        return out
    def poly_action(P,vec):
        out=[ZERO]*25
        for w,c in P.items():
            for col,(row,phase) in enumerate(wmap(w)):
                if vec[col]: out[row]=out[row]+c*phase*vec[col]
        return out
    direct=[[ZERO for _ in range(25)] for _ in range(25)]
    for row,col in itertools.product(range(25),repeat=2):
        j,k=divmod(row,5); ell,m=divmod(col,5); accum=[0]*8
        for ax,by,a,b in itertools.product(range(2),range(2),range(5),range(5)):
            weight=event2(ax,by,a,b)
            phaseA=4*a+2*ax; phaseB=-4*b+(1 if by==0 else -1)
            exponent=((j-ell)*phaseA+(k-m)*phaseB)%20
            for q,c in enumerate(ZPOW[exponent]): accum[q]+=weight*c
        direct[row][col]=E.cyc(accum)/50
    require(direct==adj(direct),'Direct Bell not Hermitian')
    from_unitaries=[[ZERO for _ in range(25)] for _ in range(25)]
    for w,c in B.items():
        for col,(row,phase) in enumerate(wmap(w)): from_unitaries[row][col]=from_unitaries[row][col]+c*phase
    require(direct==from_unitaries,'Direct event Bell differs from Fourier-operator Bell')
    note('physical_measurements_and_Bell',{'rank_one_projectors_rebuilt':20,'local_projector_matrix_entries':500,'PVM_pair_products_checked':orthogonality_products,'unitary_matrix_entries_rebuilt':100,'U_fifth_powers_exact':True,'full_Bell_matrix_entries_independently_matched':625,'projector_Bell_source':'100 signed original setting/outcome coefficients; denominator 50; z exponent arithmetic'})

    # Match the serialized polynomial state to the manuscript's rational formulas by cross multiplication.
    gamma=[decode(c) for c in data['sos']['gamma']]
    require(gamma==[decode(c) for c in data['kernels']['gamma']],'State serialization mismatch')
    f=[ZERO,u*(5-s)/20,(s-1)/2,s*u/10,(s+1)/2]
    require(f==[decode(c) for c in data['kernels']['fourier_reduced_entries']],'Toeplitz entries serialization')
    require((u/2)*f[1]==ONE and s*f[3]==u/2,'No unverified algebraic division for f1/f3')
    den=mu*(mu-f[2])-2*f[1]*f[1]
    num=mu*(f[1]+f[3])+2*f[1]*f[2]
    require(gamma[0]==1 and gamma[4]==1 and gamma[1]==gamma[3],'State shape')
    require(gamma[1]*den==num and gamma[2]*mu==2*(f[2]+f[1]*gamma[1]),'State formula cross products')
    # Analytic proof: mu>3, 0<f1,f2<1 => den>3(3-1)-2=4; all state numerators positive.
    require(boxes['mu'][0]>3 and boxes['sqrt5'][0]>2 and boxes['sqrt5'][1]<3 and boxes['u'][0]>2,'Bounds needed for nonzero denominators')
    gamma_bounds=[real_tower_interval(c,boxes) for c in data['sos']['gamma']]
    require(all(v[0]>0 for v in gamma_bounds),'State amplitude positivity')
    norm=sum((g.conj()*g for g in gamma),ZERO)
    require(norm==decode(data['positivity']['physical_strategy']['normalization_squared']),'Normalization serialization mismatch')
    for i,g in enumerate(gamma): require(g==g.conj(),'Nonreal gamma')
    require(norm==2+2*gamma[1]**2+gamma[2]**2,'Normalization formula')
    for j,k in itertools.product(range(5),repeat=2): require(direct[6*j][6*k]==f[abs(j-k)],'Toeplitz compression mismatch')
    leakage=0
    for row in range(25):
        if row//5!=row%5:
            for j in range(5):
                require(direct[row][6*j]==ZERO,'Bell escapes correlated subspace');leakage+=1
    vec=[ZERO]*25
    for j,g in enumerate(gamma): vec[6*j]=g
    residual=[sum((direct[i][j]*vec[j] for j in range(25)),ZERO)-mu*vec[i] for i in range(25)]
    require(not any(residual),'25D eigenvector residual')
    sos_annihilation=0
    for R in polys:
        require(not any(poly_action(R,vec)),'R does not annihilate claimed attaining state')
        Radj={wa(w):c.conj() for w,c in R.items()}
        require(not any(poly_action(Radj,vec)),'R* does not annihilate claimed attaining state')
        sos_annihilation+=2
    kernel_annihilation=0
    for key,Eb in Eblocks.items():
        for j in range(len(Eb[0])):
            P={Q[i]:Eb[i][j].conj() for i in range(81) if Eb[i][j]}
            require(not any(poly_action(P,vec)),f'Kernel action failure {key}/{j}')
            require(not any(poly_action({wa(w):c.conj() for w,c in P.items()},vec)),f'Adjoint kernel action failure {key}/{j}')
            kernel_annihilation+=2
    note('exact_attainment',{'state_formula_cross_multiplications':True,'state_amplitudes_strictly_positive':True,'a_denominator_strictly_greater_than':4,'normalization_formula_exact':True,'Toeplitz_entries_checked':25,'off_subspace_entries_checked':leakage,'full_eigenvector_residual_coordinates':25,'nonzero_eigenvector_residual_coordinates':0,'R_and_adjoint_annihilation_vectors':sos_annihilation,'R_and_adjoint_annihilation_coordinates':sos_annihilation*25,'kernel_and_adjoint_annihilation_vectors':kernel_annihilation,'gamma_display':[format(float((v[0]+v[1])/2),'.17g') for v in gamma_bounds]})

    # Parameter metadata is not needed for the proof, but all entries can be checked against H.
    parameters=[decode(v) for v in data['candidate']['parameters']]
    require(len(parameters)==len(data['candidate']['meta'])==42,'Parameter metadata length')
    rebuilt={str(key):[[ZERO for _ in H] for _ in H] for key,H in data['candidate']['H'].items()}
    for p,(key,i,j,kind) in zip(parameters,data['candidate']['meta']):
        key=str(key);require(p==p.conj(),'Parameter must be real')
        if kind=='D': rebuilt[key][i][i]=rebuilt[key][i][i]+p
        elif kind=='R':
            rebuilt[key][i][j]=rebuilt[key][i][j]+p;rebuilt[key][j][i]=rebuilt[key][j][i]+p
        elif kind=='I':
            rebuilt[key][i][j]=rebuilt[key][i][j]+ii*p;rebuilt[key][j][i]=rebuilt[key][j][i]-ii*p
        else: raise AssertionError('Unknown parameter kind')
    for key,H in data['candidate']['H'].items(): require(rebuilt[key]==[[decode(c) for c in row] for row in H],'Parameter metadata/H mismatch')
    note('parameter_metadata',{'all_42_parameters_match_H':True,'discovery_rank_and_search_convergence':'not relied upon and not independently re-established'})


def load(root):
    names={'sos':'SOS14.json','candidate':'EXACT_SOS_CANDIDATE.json','positivity':'POSITIVITY_CERTIFICATE.json','kernels':'EXACT_KERNELS.json'}
    return {k:json.loads((root/'candidate'/fn).read_text()) for k,fn in names.items()}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root',type=Path)
    parser.add_argument('--stage',choices=['basic','sos','full'],default='full')
    parser.add_argument('--out',type=Path,default=Path(__file__).parent/'audit_results.json')
    args=parser.parse_args(); data=load(args.root)
    boxes,B,Q,universe=basic(args.root,data)
    weights,bounds=positivity(data,boxes)
    if args.stage!='basic':
        polys,summed=sos_identity(data,B,Q,weights)
    if args.stage=='full':
        extended(data,boxes,B,Q,weights,bounds,polys,summed)
    RESULTS['elapsed_seconds']=time.perf_counter()-T0
    args.out.write_text(json.dumps(RESULTS,ensure_ascii=False,indent=2))
    print('ALL REQUESTED EXACT CHECKS PASSED',flush=True)

if __name__=='__main__': main()
