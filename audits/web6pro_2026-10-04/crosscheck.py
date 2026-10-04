#!/usr/bin/env python3
"""Second standalone exact check. Uses a radical-tower basis and adjacent-word rewriting.

Unlike audit.py this does not use cyclotomic reduction or split words by party.
The target Bell polynomial is reconstructed from all 100 original event coefficients,
using the inverse spectral-projector transform. Root enclosures are freshly bisected.
Python >=3.10, standard library only. No import from audit.py or candidate programs.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from pathlib import Path
import argparse,json,math,time
if not __debug__:
    raise RuntimeError("Run this checker without Python -O: assertions are required.")
START=time.perf_counter()
BASIS=[(j%2,(j//2)%3,(j//6)%2,j//12) for j in range(24)]

def adddict(dst,src,mult=1):
    for j,c in src: dst[j]+=mult*c

@lru_cache(None)
def reduce_exp(a,b,c,e):
    ans=defaultdict(int)
    if e>=2:
        adddict(ans,reduce_exp(a,b,c,e%2),(-1)**(e//2))
    elif c>=2:
        adddict(ans,reduce_exp(a,b,c-2,e),10)
        adddict(ans,reduce_exp(a+1,b,c-2,e),2)
    elif b>=3:
        adddict(ans,reduce_exp(a+1,b-1,c,e),5)
        adddict(ans,reduce_exp(a,b-2,c,e),100)
        adddict(ans,reduce_exp(a+1,b-2,c,e),-20)
        adddict(ans,reduce_exp(a,b-3,c,e),500)
        adddict(ans,reduce_exp(a+1,b-3,c,e),-200)
    elif a>=2:
        adddict(ans,reduce_exp(a%2,b,c,e),5**(a//2))
    else: ans[a+2*b+6*c+12*e]=1
    return tuple((j,c) for j,c in ans.items() if c)
PRODUCTS=[[reduce_exp(*(a+b for a,b in zip(left,right))) for right in BASIS] for left in BASIS]

class R:
    __slots__=('n','d','nz')
    def __init__(self,nums,den=1):
        assert len(nums)==24 and den>0
        g=math.gcd(den,*nums)
        self.n=tuple(n//g for n in nums); self.d=den//g
        self.nz=tuple((j,c) for j,c in enumerate(self.n) if c)
    def __bool__(self): return bool(self.nz)
    def __eq__(self,other): return self.n==other.n and self.d==other.d
    def __neg__(self): return R([-v for v in self.n],self.d)
    def __add__(self,other):
        if not self:return other
        if not other:return self
        g=math.gcd(self.d,other.d); a=other.d//g;b=self.d//g
        return R([a*v+b*w for v,w in zip(self.n,other.n)],self.d*a)
    def __sub__(self,other):return self+-other
    def __mul__(self,other):
        if not self or not other:return ZERO
        nums=[0]*24
        for j,v in self.nz:
            for k,w in other.nz:
                t=v*w
                for h,m in PRODUCTS[j][k]:nums[h]+=m*t
        return R(nums,self.d*other.d)
    def scale(self,q):
        q=Q(q);return R([q.numerator*v for v in self.n],q.denominator*self.d)
    def conj(self):return R([v if j<12 else -v for j,v in enumerate(self.n)],self.d)
    def power(self,n):
        out=ONE
        for _ in range(n):out=out*self
        return out

def unit(j):return R([int(k==j) for k in range(24)])
ZERO=R([0]*24);ONE=unit(0);s=unit(1);x=unit(2);u=unit(6);i=unit(12)
z=(u+i*(s-ONE)).scale(Q(1,4));omega=z.power(4);mu=x.scale(Q(1,5))
wp=[omega.power(k) for k in range(5)]
assert z.power(5)==i and omega.power(5)==ONE

def decode(o):
    assert len(o['n'])==24 and int(o['d'])>0
    return R(tuple(map(int,o['n'])),int(o['d']))

@lru_cache(None)
def normal(raw):
    w=[(int(r),int(k)%5) for r,k in raw if int(k)%5]
    assert all(0<=r<4 for r,k in w)
    j=0
    while j+1<len(w):
        (a,b),(c,d)=w[j:j+2]
        if a==c:
            exp=(b+d)%5
            w[j:j+2]=[(a,exp)] if exp else []
            j=max(0,j-1)
        elif a%2==1 and c%2==0:
            w[j],w[j+1]=w[j+1],w[j]
            j=max(0,j-1)
        else:j+=1
    return tuple(w)

def adj(w):return normal(tuple((r,-k) for r,k in reversed(w)))
def mulword(a,b):return normal(a+b)
def inc(P,w,c):P[w]=P.get(w,ZERO)+c

def p(t):return 5*t**6-65*t**4+144*t**2+96*t+16

def bisect(f,lo,hi,bits=300):
    assert f(lo)<0<f(hi)
    for _ in range(bits):
        mid=(lo+hi)/2
        if f(mid)<0:lo=mid
        else:hi=mid
    assert f(lo)<0<f(hi)
    return lo,hi

def times(a,b):
    q=[v*w for v in a for w in b];return min(q),max(q)
def power(a,n):
    v=(Q(1),Q(1))
    for _ in range(n):v=times(v,a)
    return v

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root',type=Path)
    parser.add_argument('--out',type=Path,default=Path(__file__).parent/'crosscheck_results.json')
    args=parser.parse_args()
    source=args.root/'candidate'/'SOS14.json'
    data=json.loads(source.read_text())
    # Fresh enclosures: do not read embedding_boxes.
    mb=bisect(p,Q(3),Q(31,10))
    sb=bisect(lambda t:t*t-5,Q(2),Q(3))
    ul=bisect(lambda t:t*t-10-2*sb[0],Q(3),Q(4))[0]
    uh=bisect(lambda t:t*t-10-2*sb[1],Q(3),Q(4))[1]
    ub=ul,uh;xb=5*mb[0],5*mb[1]
    assert ul*ul<10+2*sb[0] and uh*uh>10+2*sb[1]
    positive=[];weight_elements=[]
    for term in data['terms']:
        w=decode(term['weight']);assert w==w.conj() and not any(w.n[12:])
        lo=hi=Q(0)
        for j,c in enumerate(w.n[:12]):
            a,b,e,_=BASIS[j]
            interval=times(times(power(sb,a),power(xb,b)),power(ub,e))
            part=times(interval,(Q(c,w.d),Q(c,w.d)))
            lo+=part[0];hi+=part[1]
        assert lo>Q(1,3000)
        positive.append(lo);weight_elements.append(w)
    print(f'{time.perf_counter()-START:.2f}s Fresh 300-step root boxes and all 14 weight bounds > 1/3000',flush=True)

    # Independently construct the exact signed event coefficient table from the eight event types.
    coef={(ax,by,a,b):0 for ax,by,a,b in product(range(2),range(2),range(5),range(5))}
    for a,k in product(range(5),range(2)):
        w=2-k
        for ax,by,b,sign in [(0,0,a-k,1),(1,0,a+k+1,1),(1,1,a-k,1),(0,1,a+k,1),
                              (0,0,a+k+1,-1),(1,0,a-k,-1),(1,1,a+k+1,-1),(0,1,a-k-1,-1)]:
            coef[ax,by,a,b%5]+=w*sign
    bell={}
    for ax,by,k,ell in product(range(2),range(2),range(5),range(5)):
        c=ZERO
        for a,b in product(range(5),repeat=2):
            c=c+wp[(-k*(a+ax)-ell*(b+by))%5].scale(coef[ax,by,a,b])
        inc(bell,normal(((2*ax,k),(2*by+1,ell))),c.scale(Q(1,50)))
    target={w:-c for w,c in bell.items()};inc(target,(),mu)
    assert sum(bool(c) for c in bell.values())==16
    assert all(bell.get(adj(w),ZERO)==c.conj() for w,c in bell.items())
    total={};count=0
    for term,d in zip(data['terms'],weight_elements):
        coeffs=[]
        for v in term['polynomial']:
            raw=tuple((int(r),int(k)) for r,k in v['word']);coeffs.append((normal(raw),decode(v['coefficient'])))
        for wa,ca in coeffs:
            for wb,cb in coeffs:
                inc(total,mulword(adj(wa),wb),d*(ca.conj()*cb));count+=1
                # Separate products, rather than transposing/relabeling the first summation.
                inc(total,mulword(wa,adj(wb)),d*(ca*cb.conj()));count+=1
        print(f'{time.perf_counter()-START:.2f}s Radical-tower expansion {term["id"]}',flush=True)
    touched=set(total)|set(target)
    residual=[w for w in touched if total.get(w,ZERO)!=target.get(w,ZERO)]
    assert not residual,residual[:5]
    # Count only positions from expansion and genuinely nonzero target coefficients.
    active=set(total)|{w for w,c in target.items() if c}
    result={'arithmetic':'radical tower; four direct polynomial relations; integer numerators and common positive denominator',
      'word_reduction':'adjacent interchange only for Bob-followed-by-Alice; adjacent identical-generator merging modulo 5',
      'Bell_target':'inverse spectral-projector transform of original 100 signed event coefficients; not the f(z) formula',
      'root_boxes':'fresh 300 bisections; serialized embedding boxes not read',
      'all_14_weights_strictly_greater_than':'1/3000','minimum_rational_lower_bound':str(min(positive)),
      'terms':len(data['terms']),'raw_products':count,'active_word_positions':len(active),
      'all_positions_including_zero_fourier_targets':len(touched),'nonzero_exact_residual_words':len(residual),
      'elapsed_seconds':time.perf_counter()-START}
    args.out.write_text(json.dumps(result,indent=2,ensure_ascii=False))
    print(json.dumps({k:v for k,v in result.items() if k!='minimum_rational_lower_bound'},indent=2),flush=True)
    print('SECOND STANDALONE EXACT CHECK PASSED',flush=True)

if __name__=='__main__':main()
