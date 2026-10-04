"""Independent bounded algebra audit. No supplied verifier code is imported.

Run with the standard library Python runtime supplied for the task.
All mathematical inputs come exclusively from audit_view.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from decimal import Decimal, localcontext
from itertools import product
import argparse, hashlib, json, math, time, sys

sys.dont_write_bytecode = True
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parents[2]/'audit_view')
parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
args=parser.parse_args()
ROOT=args.input_dir.resolve()
OUT=args.output_dir.resolve()
OUT.mkdir(parents=True,exist_ok=True)
started = time.monotonic()

def require(b, msg):
    if not b:
        raise AssertionError(msg)

def parseint(a):
    require(type(a) is int or (isinstance(a, str) and a.lstrip('-').isdigit()), 'nonintegral serialized number')
    return int(a)

EXPS = [(a,b,c,e) for e in range(2) for c in range(2) for b in range(3) for a in range(2)]
def index(a,b,c,e): return a+2*b+6*c+12*e

@lru_cache(None)
def monomial(a,b,c,e):
    """Reduce using only s^2=5, x^3=5sx^2+(100-20s)x+500-200s,
    u^2=10+2s and i^2=-1. No cyclotomic conversions.
    """
    out = [0]*24
    if b >= 3:
        branch = [(5,a+1,b-1,c,e),(100,a,b-2,c,e),(-20,a+1,b-2,c,e),
                  (500,a,b-3,c,e),(-200,a+1,b-3,c,e)]
    elif c >= 2:
        branch = [(10,a,b,c-2,e),(2,a+1,b,c-2,e)]
    elif a >= 2:
        branch = [(5,a-2,b,c,e)]
    elif e >= 2:
        branch = [(-1,a,b,c,e-2)]
    else:
        out[index(a,b,c,e)] = 1
        return tuple(out)
    for weight,aa,bb,cc,ee in branch:
        for j,n in enumerate(monomial(aa,bb,cc,ee)):
            out[j] += weight*n
    return tuple(out)

PRODUCT = []
for alpha in EXPS:
    row = []
    for beta in EXPS:
        v = monomial(*(a+b for a,b in zip(alpha,beta)))
        row.append(tuple((j,n) for j,n in enumerate(v) if n))
    PRODUCT.append(row)

class T:
    __slots__ = ('v','d','nz')
    def __init__(self, v=0, d=1):
        if isinstance(v,T): self.v,self.d,self.nz = v.v,v.d,v.nz; return
        if isinstance(v,F): v,d = v.numerator,v.denominator
        if isinstance(v,int): v=[v]+[0]*23
        require(len(v)==24 and d>0,'bad tower coefficient')
        g=d
        for n in v: g=math.gcd(g,n)
        self.v=tuple(n//g for n in v); self.d=d//g
        self.nz=tuple((j,n) for j,n in enumerate(self.v) if n)
    def __bool__(self): return bool(self.nz)
    def __eq__(self,b):
        b=T(b); return self.v==b.v and self.d==b.d
    def __neg__(self): return T([-n for n in self.v],self.d)
    def __add__(self,b):
        b=T(b)
        if not self: return b
        if not b: return self
        d=math.lcm(self.d,b.d)
        return T([a*(d//self.d)+bb*(d//b.d) for a,bb in zip(self.v,b.v)],d)
    __radd__=__add__
    def __sub__(self,b): return self+-T(b)
    def __rsub__(self,b): return T(b)+-self
    def __mul__(self,b):
        b=T(b)
        if not self or not b: return ZERO
        out=[0]*24
        for j,a in self.nz:
            for k,bb in b.nz:
                for t,n in PRODUCT[j][k]: out[t]+=a*bb*n
        return T(out,self.d*b.d)
    __rmul__=__mul__
    def __pow__(self,k):
        require(type(k) is int and k>=0,'bad power')
        out=ONE
        for _ in range(k): out=out*self
        return out
    def bar(self): return T([n if j<12 else -n for j,n in enumerate(self.v)],self.d)
    def scale(self,n,d=1): return T([n*a for a in self.v],self.d*d)

ZERO=T(); ONE=T(1)
def gen(a,b,c,e): return T(monomial(a,b,c,e))
S=gen(1,0,0,0); X=gen(0,1,0,0); U=gen(0,0,1,0); I=gen(0,0,0,1)
MU=X.scale(1,5); Z=(U+I*(S-1)).scale(1,4)
ZS=[Z**a for a in range(21)]

def scalar(o):
    ns=[parseint(n) for n in o['n']]; d=parseint(o['d'])
    require(len(ns)==24 and d>0,'bad scalar serialization')
    return T(ns,d)

def mat(o): return [[scalar(x) for x in row] for row in o]

# Group elements are PAIRS of reduced syllable lists, not a flattened word.
# Each list is the reduced normal form in C5 * C5. Multiplication preserves
# same-party order and uses cross-party commutation only to separate parties.
UNIT=((),())
def reduce_syllables(seq):
    stack=[]
    for r,k in seq:
        require(type(r) is int and 0<=r<4 and type(k) is int,'bad generator')
        k%=5
        if not k: continue
        if stack and stack[-1][0]==r:
            _,l=stack.pop(); k=(k+l)%5
        if k: stack.append((r,k))
    return tuple(stack)
def word(raw):
    return tuple(reduce_syllables((r,k) for r,k in raw if r%2==p) for p in range(2))
def mul(a,b): return tuple(reduce_syllables(a[p]+b[p]) for p in range(2))
def dagger(a): return tuple(reduce_syllables((r,-k) for r,k in reversed(a[p])) for p in range(2))
def addto(acc,w,x): acc[w]=acc.get(w,ZERO)+x

def interval(o):
    lo=o['lower']; hi=o['upper']
    q=(F(parseint(lo['numerator']),parseint(lo['denominator'])),F(parseint(hi['numerator']),parseint(hi['denominator'])))
    require(q[0]<=q[1],'reversed interval'); return q
def plus(a,b): return a[0]+b[0],a[1]+b[1]
def times(a,b):
    v=[x*y for x in a for y in b]; return min(v),max(v)
def iscale(a,k):
    v=[a[0]*k,a[1]*k]; return min(v),max(v)
def ipower(a,k):
    out=(F(1),F(1))
    for _ in range(k): out=times(out,a)
    return out
def p(t): return 5*t**6-65*t**4+144*t*t+96*t+16
def tower_intervals(box):
    m,s,u=map(lambda k:interval(box[k]),('mu','sqrt5','u'))
    require(m[0]>3 and p(m[0])<0<p(m[1]),'bad selected mu interval')
    require(s[0]>0 and s[0]**2<5<s[1]**2,'bad positive sqrt5 interval')
    require(u[0]>0 and u[0]**2<10+2*s[0] and u[1]**2>10+2*s[1],'bad positive u interval')
    out=[]
    for a,b,c,e in EXPS:
        out.append(times(times(ipower(s,a),ipower(iscale(m,5),b)),ipower(u,c)))
    return out
def real_bounds(v,ibs):
    require(v.bar()==v,'non-real coefficient')
    out=(F(0),F(0))
    for j,n in v.nz:
        require(j<12,'imaginary term in real tower scalar')
        out=plus(out,iscale(ibs[j],F(n,v.d)))
    return out

ident=json.loads((ROOT/'INPUT_IDENTITY.json').read_text())
hashes={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in ident}
require(hashes==ident,'frozen identity mismatch')
data=json.loads((ROOT/'SOS14.json').read_text())
kernels=json.loads((ROOT/'EXACT_KERNELS.json').read_text())
gram=json.loads((ROOT/'EXACT_SOS_CANDIDATE.json').read_text())
pos=json.loads((ROOT/'POSITIVITY_CERTIFICATE.json').read_text())
schema_counts={}
def check_schema(o):
    count=0
    if isinstance(o,dict):
        if 'n' in o and 'd' in o and isinstance(o['n'],list):
            scalar(o); count+=1
        for value in o.values(): count+=check_schema(value)
    elif isinstance(o,list):
        for value in o: count+=check_schema(value)
    return count
for name,obj in [('SOS14.json',data),('EXACT_KERNELS.json',kernels),
                 ('EXACT_SOS_CANDIDATE.json',gram),('POSITIVITY_CERTIFICATE.json',pos)]:
    schema_counts[name]=check_schema(obj)

require(S*S==5 and U*U==10+2*S and I*I==-1,'tower generator relations')
require(Z**5==I and Z**10==-1 and Z**20==1,'exact zeta embedding')
require(Z**8-Z**6+Z**4-Z**2+1==0,'cyclotomic polynomial')
require(2*(ZS[2]+ZS[18])-1==S and 2*(ZS[1]+ZS[19])==U,'inverse conversion')
require(p(MU)==0,'sextic relation')

ck=[sum((ZS[(-4*k*r)%20].scale(2-r,10) for r in range(5)),ZERO) for k in range(5)]
require(ck[0]==ZERO,'Fourier constant')
for r in range(5):
    require(sum((ck[k]*ZS[(4*k*r)%20] for k in range(5)),ZERO)==T(F(2-r,2)),'Fourier synthesis')
bell={}
for r in range(4):
    for k in range(1,5):
        w=word(((r,k),((r+1)%4,-k)))
        c=ck[k]*(ZS[(-4*k)%20] if r==3 else ONE)
        addto(bell,w,c)
rhs={w:-c for w,c in bell.items()}; rhs[UNIT]=MU

ibs=tower_intervals(data['embedding_boxes'])
acc={}; weights=[]; termcount=0
for term in data['terms']:
    d=scalar(term['weight']); b=real_bounds(d,ibs)
    require(b[0]>0,'nonpositive weight '+term['id']); weights.append(b)
    poly=[(word(t['word']),scalar(t['coefficient'])) for t in term['polynomial']]
    require(len({w for w,c in poly})==len(poly),'duplicate words')
    termcount+=len(poly)
    for w,a in poly:
        for v,b in poly:
            addto(acc,mul(dagger(w),v),d*a.bar()*b)
            addto(acc,mul(w,dagger(v)),d*a*b.bar())
universe=set(acc)|set(rhs)
residuals=[w for w in universe if acc.get(w,ZERO)!=rhs.get(w,ZERO)]
require(not residuals,'independent tower SOS residual')
print('Independent tower SOS expansion exact:',len(universe),'positions;',termcount,'coefficients',flush=True)

alice=[UNIT]+[word(((r,k),)) for r in (0,2) for k in range(1,5)]
bob=[UNIT]+[word(((r,k),)) for r in (1,3) for k in range(1,5)]
q=[mul(a,b) for a in alice for b in bob]
require([word(w) for w in kernels['Q']]==q,'Q mismatch')
fullwords={mul(dagger(a),b) for a in q for b in q}
require(len(fullwords)==1681,'wrong full universe size')
require(set(rhs)<=fullwords and universe<=fullwords,'support omitted from full Gram test')
require(word(((0,1),(2,1)))!=word(((2,1),(0,1))),'accidental same-party commutation')
require(word(((1,1),(3,1)))!=word(((3,1),(1,1))),'accidental Bob commutation')
require(word(((0,1),(1,1),(0,4)))==word(((1,1),)),'cross-party commuting cancellation failure')
require(word(((0,1),(2,1),(2,4),(0,4)))==UNIT,'recursive cancellation failure')
group_laws=0
for a,b in product(q,repeat=2):
    require(dagger(mul(a,b))==mul(dagger(b),dagger(a)),'star reversal failure')
    require(mul(a,dagger(a))==UNIT,'inverse failure')
    group_laws+=1

gacc={}; pivots=[]; sizes={}
gibs=tower_intervals(pos['embedding_boxes'])
for key in gram['blocks']:
    H=mat(gram['H'][str(key)]); E=mat(kernels['kernels'][str(key)]['E'])
    L=mat(pos['blocks'][str(key)]['L']); D=[scalar(c) for c in pos['blocks'][str(key)]['D']]
    n=len(H); sizes[str(key)]=n
    require(all(len(row)==n for row in H),'H square dimension')
    require(len(E)==81 and all(len(row)==n for row in E),'E dimension')
    require(len(L)==n and len(D)==n and all(len(row)==n for row in L),'LDL dimension')
    require(all(H[a][b]==H[b][a].bar() for a in range(n) for b in range(n)),'Gram hermiticity')
    require(all(L[a][b]==(1 if a==b else 0) for a in range(n) for b in range(a,n)),'L triangular normalization')
    for a,b in product(range(n),repeat=2):
        require(H[a][b]==sum((L[a][j]*D[j]*L[b][j].bar() for j in range(n)),ZERO),'LDL reconstruction')
    for d in D:
        bounds=real_bounds(d,gibs); require(bounds[0]>0,'nonpositive Gram pivot'); pivots.append(bounds)
    nz=[i for i in range(81) if any(E[i])]
    EH={i:[sum((E[i][a]*H[a][b] for a in range(n)),ZERO) for b in range(n)] for i in nz}
    for i,j in product(nz,repeat=2):
        c=sum((EH[i][b]*E[j][b].bar() for b in range(n)),ZERO)
        addto(gacc,mul(dagger(q[i]),q[j]),c)
        addto(gacc,mul(q[i],dagger(q[j])),c.bar())
require(set(gacc)<=fullwords,'Gram writes outside checked support')
require(all(gacc.get(w,ZERO)==rhs.get(w,ZERO) for w in fullwords),'full Gram residual')
print('Independent tower Gram/LDL expansion exact:',len(fullwords),'positions;',len(pivots),'positive pivots',flush=True)

# All 576 basic product entries get a separate high-precision actual-embedding
# spot-check, and all weights and coefficients get direct decimal evaluations.
with localcontext() as ctx:
    ctx.prec=160
    lo=Decimal(3); hi=Decimal(31)/10
    for _ in range(480):
        mid=(lo+hi)/2
        if p(mid)<0: lo=mid
        else: hi=mid
    mu=(lo+hi)/2; s=Decimal(5).sqrt(); u=(10+2*s).sqrt(); x=5*mu
    nums=[s**a*x**b*u**c for a,b,c,e in EXPS]
    def evalt(t):
        re=Decimal(0); im=Decimal(0)
        for j,n in t.nz:
            v=Decimal(n)/Decimal(t.d)*nums[j]
            if j<12: re+=v
            else: im+=v
        return re,im
    maxerr=Decimal(0)
    for j,k in product(range(24),repeat=2):
        va=[0]*24; vb=[0]*24; va[j]=1; vb[k]=1
        a=evalt(T(va)); b=evalt(T(vb)); got=evalt(T(va)*T(vb))
        want=(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
        maxerr=max(maxerr,*(abs(a-b) for a,b in zip(got,want)))
    require(maxerr<Decimal('1e-120'),'actual-embedding arithmetic mismatch')
    decimal_weights=[evalt(scalar(t['weight'])) for t in data['terms']]
    require(all(r>0 and i==0 for r,i in decimal_weights),'decimal weight mismatch')
    observed={'mu':str(mu),'sqrt5':str(s),'u':str(u),'maximum_basis_product_absolute_error':str(maxerr),
              'minimum_weight':str(min(r for r,i in decimal_weights)),'basis_products_checked':576}

result={
    'scope':'Input-isolated independent tower arithmetic, 14-term SOS, full Gram, LDL and interval checks.',
    'input_hashes':hashes,
    'files_read':list(ident)+['AUDIT_CONTRACT.md','INPUT_IDENTITY.json'],
    'strict_integer_scalar_schema_checks':schema_counts,
    'exact_tower_SOS':{'word_positions':len(universe),'nonzero_serialized_coefficients':termcount,'residuals':0,
                       'weights':len(weights),'minimum_rational_lower_bound':str(min(a for a,b in weights))},
    'exact_tower_Gram':{'full_word_universe':len(fullwords),'support_inclusion_checked':True,'residuals':0,'block_dimensions':sizes},
    'exact_LDL':{'pivot_count':len(pivots),'minimum_rational_lower_bound':str(min(a for a,b in pivots))},
    'word_group_tests':{'basis_pairs':group_laws,'same_party_commutation_rejected':True,'cross_party_and_recursive_cancellations':True},
    'arithmetic_spotcheck':observed,
    'elapsed_seconds':time.monotonic()-started
}
(OUT/'independent_results.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2),flush=True)
