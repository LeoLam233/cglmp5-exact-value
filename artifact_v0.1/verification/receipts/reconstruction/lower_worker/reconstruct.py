"""Independent lower-bound reconstruction from TARGET.md only.

This script uses no project files besides TARGET.md and its own outputs.
The exact arithmetic is implemented here using Fractions; no symbolic
algebra package or candidate-specific lemma is used.
"""
from fractions import Fraction as F
from decimal import Decimal, localcontext
import hashlib
import argparse
import importlib.metadata
import json
import platform
import sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--input", type=Path,
                    default=ROOT/"TARGET.exposed.md",
                    help="Definitions/target-only input (default: included exposure copy).")
parser.add_argument("--output", type=Path, default=ROOT,
                    help="Receipt directory; defaults to this script's directory.")
args = parser.parse_args()
INPUT = args.input.resolve()
OUTPUT = args.output.resolve()
OUTPUT.mkdir(parents=True,exist_ok=True)

class Q5:
    """a+b*sqrt(5), with rational a,b."""
    def __init__(self, a=0, b=0):
        if isinstance(a, Q5):
            self.a, self.b = a.a, a.b
        else:
            self.a, self.b = F(a), F(b)
    def __add__(self, other):
        o=Q5(other); return Q5(self.a+o.a, self.b+o.b)
    __radd__=__add__
    def __neg__(self): return Q5(-self.a,-self.b)
    def __sub__(self, other): return self+-Q5(other)
    def __rsub__(self, other): return Q5(other)+-self
    def __mul__(self, other):
        o=Q5(other)
        return Q5(self.a*o.a+5*self.b*o.b, self.a*o.b+self.b*o.a)
    __rmul__=__mul__
    def __eq__(self, other):
        o=Q5(other); return self.a==o.a and self.b==o.b
    def __repr__(self): return f"({self.a})+({self.b})*sqrt(5)"
    def conjugate(self): return Q5(self.a,-self.b)

def trim(a):
    a=list(a)
    while len(a)>1 and a[-1]==0: a.pop()
    return a
def padd(a,b):
    return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
                 for i in range(max(len(a),len(b)))])
def pneg(a): return [-x for x in a]
def psub(a,b): return padd(a,pneg(b))
def pmul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]=out[i+j]+x*y
    return trim(out)
def peval(a,x):
    z=0
    for c in reversed(a): z=z*x+c
    return z
def pdivrem(a,b):
    a=trim(a); b=trim(b); q=[F(0)]*max(1,len(a)-len(b)+1)
    while len(a)>=len(b) and a!=[0]:
        j=len(a)-len(b); z=a[-1]/b[-1]; q[j]+=z
        a=psub(a,[F(0)]*j+[z*x for x in b])
    return trim(q),trim(a)
def sturm(p):
    seq=[p,[i*p[i] for i in range(1,len(p))]]
    while seq[-1]!=[0]:
        _,r=pdivrem(seq[-2],seq[-1])
        if r==[0]: break
        seq.append(pneg(r))
    return seq
def sign(x): return (x>0)-(x<0)
def changes(signs):
    s=[x for x in signs if x]
    return sum(a!=b for a,b in zip(s,s[1:]))
def variations(seq,x): return changes([sign(peval(p,x)) for p in seq])
def vinf(seq,positive=True):
    return changes([sign(p[-1])*(1 if positive or (len(p)-1)%2==0 else -1)
                    for p in seq])
def dfrac(f): return Decimal(f.numerator)/Decimal(f.denominator)
def q_interval(q,lo,hi):
    return (q.a+q.b*(lo if q.b>=0 else hi),
            q.a+q.b*(hi if q.b>=0 else lo))

log=[]
def note(k,v): log.append(f"{k}: {v}")
target_hash=hashlib.sha256(INPUT.read_bytes()).hexdigest()
note("INPUT SHA-256",target_hash)
note("Python",sys.version)
note("platform",platform.platform())
note("numpy",np.__version__)
note("exact arithmetic","fractions.Fraction, custom Q(sqrt(5)), custom rational Sturm chain")
note("external sources read","none")
note("exposure","TARGET.md definitions and sextic/largest-root value; parent task boundary, Python path; no witness, proof, candidate files, project memory, other agent results")

s=Q5(0,1)
c2=(s-1)*F(1,2)
c4=(s+1)*F(1,2)
c1sq=(5-s)*F(1,10)
c1c3=s*F(1,5)
h=(3+s)*F(1,2) # c1+c3 = c1*h
# Characteristic polynomial of reflection-symmetric restriction, ascending.
f=[-4+s*F(8,5), -4+s*F(4,5), -s, Q5(1)]
g=[s*F(2,5),s,Q5(1)]
trace=c4+c2
principal_sum=c4*c2-c1sq*h*h-2*c2*c2-2*c1sq
det=4*c1sq*h*c2-2*c4*c1sq-2*c2*c2*c2
assert f==[-det,principal_sum,-trace,Q5(1)]
assert g==[c4*c2-c1sq*(1-c4)*(1-c4),c4+c2,Q5(1)]
norm=pmul(f,[x.conjugate() for x in f])
p=[F(16),F(96),F(144),F(0),F(-65),F(0),F(5)]
assert [5*x for x in norm]==[Q5(x) for x in p]
note("symmetric characteristic, ascending",f)
note("antisymmetric characteristic, ascending",g)
note("full five-dimensional characteristic, ascending",pmul(f,g))
note("5*f_s*f_-s equals exposed p",True)

# Exact polynomial eigenvector. b=c1*B; a,c lie in Q(s)[t].
D=[-2*c1sq,-c2,Q5(1)]
B=[2*c2,h]
C=padd(pmul([2*c2],[-c2,Q5(1)]),[2*c1sq*h])
ra=psub(psub(pmul([-c4,Q5(1)],D),pmul([c1sq*h],B)),pmul([c2],C))
rb=psub(psub(pmul([-c2,Q5(1)],B),pmul([h],D)),C)
rc=psub(psub(pmul([0,Q5(1)],C),pmul([2*c2],D)),pmul([2*c1sq],B))
assert ra==f and rb==[0] and rc==[0]
note("exact eigenvector residuals",{"row a":"f_s(t)","row b":"0", "row c":"0"})

# Rational Sturm computation, and rational enclosure of sqrt(5), identify
# the attained root as the largest real root of the supplied sextic.
L=F(2236067977499789,10**15)
U=F(2236067977499790,10**15)
assert L*L<5<U*U
a=F(301571,100000)
b=F(301572,100000)
fa=q_interval(peval(f,Q5(a)),L,U)
fb=q_interval(peval(f,Q5(b)),L,U)
assert fa[1]<0 and fb[0]>0
chain=sturm(p)
assert peval(p,a)!=0 and peval(p,b)!=0
va=variations(chain,a); vb=variations(chain,b); vp=vinf(chain)
assert va-vb==1 and vb-vp==0
note("sqrt(5) rational enclosure",[str(L),str(U)])
note("root interval",[str(a),str(b)])
note("f_s(a) exact bounds",[str(x) for x in fa])
note("f_s(b) exact bounds",[str(x) for x in fb])
note("Sturm V(a),V(b),V(+infty)",[va,vb,vp])
note("Sturm root counts",{"in interval":va-vb,"above interval":vb-vp})
note("Sturm sequence ascending",[[str(x) for x in r] for r in chain])

with localcontext() as ctx:
    ctx.prec=90
    ds=Decimal(5).sqrt()
    def df(t): return t**3-ds*t**2+(-4+4*ds/5)*t-4+8*ds/5
    al=dfrac(a); bu=dfrac(b)
    for _ in range(270):
        mid=(al+bu)/2
        if df(mid)<0: al=mid
        else: bu=mid
    lam=(al+bu)/2
    dc1=((5-ds)/10).sqrt(); dc2=(ds-1)/2; dc4=(ds+1)/2
    dc3=((5+ds)/10).sqrt()
    da=lam**2-dc2*lam-2*dc1**2
    db=lam*(dc1+dc3)+2*dc1*dc2
    dc=2*dc2*(lam-dc2)+2*dc1*(dc1+dc3)
    dn=(2*da**2+2*db**2+dc**2).sqrt()
    coeff=[da/dn,db/dn,dc/dn,db/dn,da/dn]
    note("independently computed root (Decimal)",str(lam))
    note("state coefficients (Decimal)",[str(x) for x in coeff])
    z=np.array([float(x) for x in coeff])

d=5
alpha=[0,0.5]; beta=[0.25,-0.25]
j=np.arange(d)
UA=[np.exp(2j*np.pi*np.outer(j,j+ax)/d)/np.sqrt(d) for ax in alpha]
VB=[np.exp(2j*np.pi*np.outer(j,-j+by)/d)/np.sqrt(d) for by in beta]
psi=np.zeros(d*d,dtype=complex)
for ii in range(d): psi[ii*d+ii]=z[ii]
probs=np.empty((2,2,d,d))
unitary=[]
for M in UA+VB: unitary.append(float(np.linalg.norm(M.conj().T@M-np.eye(d))))
for x in range(2):
    for y in range(2):
        for aa in range(d):
            for bb in range(d):
                w=np.kron(UA[x][:,aa],VB[y][:,bb])
                probs[x,y,aa,bb]=abs(np.vdot(w,psi))**2

# Directly implement all eight event arms of the exposed inequality.
def event(x,y,offset):
    return sum(probs[x,y,aa,bb] for aa in range(d) for bb in range(d)
               if (aa-bb-offset)%d==0)
arms=[]
direct=0.0
Bell=np.zeros((d*d,d*d),dtype=complex)
for k in [0,1]:
    weight=1-k/2
    terms=[(0,0,k,1),(1,0,-k-1,1),(1,1,k,1),(0,1,-k,1),
           (0,0,-k-1,-1),(1,0,k,-1),(1,1,-k-1,-1),(0,1,k+1,-1)]
    values=[]
    for x,y,off,sgn in terms:
        ev=event(x,y,off); values.append(ev); direct+=weight*sgn*ev
        for aa in range(d):
            for bb in range(d):
                if (aa-bb-off)%d==0:
                    w=np.kron(UA[x][:,aa],VB[y][:,bb])
                    Bell+=weight*sgn*np.outer(w,w.conj())
    arms.append({"k":k,"weight":weight,"event probabilities in exposed order":values})

# Independently construct the real Toeplitz restriction via cosine sum.
T=np.zeros((d,d))
for ii in range(d):
    for jj in range(d):
        r=ii-jj
        T[ii,jj]=4/d*sum((1-k/2)*(np.cos(2*np.pi*r*(k+0.25)/d)
                            -np.cos(2*np.pi*r*(k+0.75)/d)) for k in [0,1])
expected=np.zeros((d,d))
for ii in range(d):
    for jj in range(d):
        if ii!=jj: expected[ii,jj]=1/(2*np.cos(np.pi*(ii-jj)/10))
ids=[ii*d+ii for ii in range(d)]
restriction=Bell[np.ix_(ids,ids)]
offids=[ii for ii in range(d*d) if ii not in ids]
results={
    "input_sha256":target_hash,
    "outcome":"PARTIAL",
    "independent_numeric_root":str(lam),
    "state_coefficients":[str(x) for x in coeff],
    "measurement_alpha":alpha,"measurement_beta":beta,
    "norm_psi_error":float(abs(np.vdot(psi,psi)-1)),
    "basis_unitarity_errors":unitary,
    "probability_normalization_errors":np.abs(probs.sum(axis=(2,3))-1).tolist(),
    "minimum_probability":float(probs.min()),
    "direct_I5":float(direct),
    "direct_I5_minus_numeric_root":float(direct-float(lam)),
    "bell_expectation":float(np.vdot(psi,Bell@psi).real),
    "bell_hermiticity_error":float(np.linalg.norm(Bell-Bell.conj().T)),
    "bell_eigenvector_residual":float(np.linalg.norm(Bell@psi-float(lam)*psi)),
    "diagonal_subspace_leakage":float(np.linalg.norm(Bell[np.ix_(offids,ids)])),
    "restriction_vs_cosine_error":float(np.linalg.norm(restriction-T)),
    "cosine_vs_closed_form_error":float(np.linalg.norm(T-expected)),
    "toeplitz_eigenvector_residual":float(np.linalg.norm(T@z-float(lam)*z)),
    "toeplitz_eigenvalues":np.linalg.eigvalsh(T).tolist(),
    "event_arms":arms,
    "exact_sturm_counts":{"in_interval":va-vb,"above_interval":vb-vp},
    "root_interval":[str(a),str(b)],
    "limitations":"An attainable lower bound is proved. No bound for other POVMs, dimensions, or states is proved. Full exposed supremum theorem remains unproved by this worker.",
}
assert max(unitary)<1e-12
assert results["norm_psi_error"]<1e-12
assert results["bell_eigenvector_residual"]<1e-12
assert results["restriction_vs_cosine_error"]<1e-12
assert results["cosine_vs_closed_form_error"]<1e-12
assert abs(results["direct_I5_minus_numeric_root"])<1e-12
OUTPUT.joinpath("checks.json").write_text(json.dumps(results,indent=2),encoding="utf-8")
OUTPUT.joinpath("exact_computation.log").write_text("\n".join(log)+"\n",encoding="utf-8")
print(json.dumps({k:v for k,v in results.items() if k not in ["event_arms","state_coefficients"]},indent=2))
print("all asserted exact and numerical checks passed")
