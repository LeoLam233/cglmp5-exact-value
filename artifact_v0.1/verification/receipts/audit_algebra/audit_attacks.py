"""Concrete bounded attack controls: altered certificates and noncommuting matrices.

The altered-certificate section deliberately invokes supplied checkers.
The matrix section uses its own Decimal evaluation of tower coefficients and
NumPy matrix operations, without checker scalar arithmetic or word reduction.
"""
from pathlib import Path
from decimal import Decimal, localcontext
import argparse, copy, importlib.util, json, math, sys, contextlib, io
sys.dont_write_bytecode=True
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parents[2]/'audit_view')
parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
args=parser.parse_args(); root=args.input_dir.resolve(); out=args.output_dir.resolve()
out.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(root))
import verify_independent as v
import verify_sos14 as sos
data=json.loads((root/'SOS14.json').read_text())
kernels=json.loads((root/'EXACT_KERNELS.json').read_text())
gram=json.loads((root/'EXACT_SOS_CANDIDATE.json').read_text())
proof=json.loads((root/'POSITIVITY_CERTIFICATE.json').read_text())
attacks=[]
def expect_reject(name, f):
    try:
        with contextlib.redirect_stdout(io.StringIO()): f()
    except (ArithmeticError, AssertionError, ValueError, KeyError, TypeError) as e:
        attacks.append({'attack':name,'rejected':True,'diagnostic':str(e)})
    else:
        attacks.append({'attack':name,'rejected':False})
        raise AssertionError('negative control unexpectedly accepted: '+name)
def mutate_sos(name, mutate):
    mutant=copy.deepcopy(data); mutate(mutant)
    target=out/'mutants'/name; target.mkdir(parents=True,exist_ok=True)
    (target/'SOS14.json').write_text(json.dumps(mutant))
    expect_reject(name,lambda:sos.verify(target,quiet=True))
def add_unit(o,j=0): o['n'][j]=str(int(o['n'][j])+int(o['d']))
mutate_sos('coefficient_plus_one',lambda d:add_unit(d['terms'][0]['polynomial'][0]['coefficient']))
mutate_sos('negative_weight',lambda d:d['terms'][0]['weight'].update(n=[str(-int(n)) for n in d['terms'][0]['weight']['n']]))
mutate_sos('imaginary_weight',lambda d:add_unit(d['terms'][0]['weight'],12))
mutate_sos('dropped_term',lambda d:d['terms'].pop())
def badmu(d):
    d['embedding_boxes']['mu']={'lower':{'numerator':'2','denominator':'1'},'upper':{'numerator':'3','denominator':'1'}}
mutate_sos('wrong_root_box',badmu)
def badsqrt(d):
    d['embedding_boxes']['sqrt5']={'lower':{'numerator':'-3','denominator':'1'},'upper':{'numerator':'-2','denominator':'1'}}
mutate_sos('negative_sqrt5_branch',badsqrt)
def badlabel(d):
    for t in d['terms']:
        for q in t['polynomial']:
            for factor in q['word']:
                if factor[0]==0:
                    factor[0]=2; return
    raise AssertionError('no Alice0 factor')
mutate_sos('same_party_generator_relabel',badlabel)
g=copy.deepcopy(gram); add_unit(g['H']['1'][0][0])
expect_reject('Gram_diagonal_plus_one',lambda:v.verify_words(kernels,g))
p=copy.deepcopy(proof); add_unit(p['blocks']['1']['L'][0][0])
expect_reject('LDL_diagonal_not_one',lambda:v.verify_positive(gram,p))
oldmu=sos.MU
try:
    sos.MU=v.C(2)
    expect_reject('false_universal_bound_2_direct',lambda:sos.verify(root,quiet=True))
finally: sos.MU=oldmu
oldmu=v.MU
try:
    v.MU=v.C(2)
    expect_reject('false_universal_bound_2_Gram',lambda:v.verify_words(kernels,gram))
finally: v.MU=oldmu

# An actual non-load-bearing parser robustness issue: int(0.5) silently yields
# zero. This input violates the certificate's stated integer scalar schema.
# It does not change the decoded original mathematical certificate.
malformed=copy.deepcopy(data)
location=None
for i,t in enumerate(malformed['terms']):
    for j,q in enumerate(t['polynomial']):
        for k,n in enumerate(q['coefficient']['n']):
            if int(n)==0:
                q['coefficient']['n'][k]=0.5; location=[i,j,k]; break
        if location is not None: break
    if location is not None: break
assert location is not None
target=out/'mutants'/'nonintegral_n_accepted'; target.mkdir(parents=True,exist_ok=True)
(target/'SOS14.json').write_text(json.dumps(malformed))
with contextlib.redirect_stdout(io.StringIO()): malformed_result=sos.verify(target,quiet=True)
schema_issue={'location_terms_polynomial_n':location,'literal_before':'0','literal_after':0.5,
              'supplied_checker_status':malformed_result['status'],
              'scope':'The input is outside the stated integer schema. int(0.5) decodes it as zero. Original scalar bytes are strictly schema checked separately; this gives no false bound for them.'}

import numpy as np
rng=np.random.default_rng(20261004)
omega=np.exp(2j*np.pi/5)
with localcontext() as ctx:
    ctx.prec=140
    s=Decimal(5).sqrt(); u=(10+2*s).sqrt()
    lo=Decimal(3); hi=Decimal(31)/10
    for _ in range(430):
        mid=(lo+hi)/2
        val=5*mid**6-65*mid**4+144*mid**2+96*mid+16
        if val<0: lo=mid
        else: hi=mid
    mu=(lo+hi)/2; x=5*mu
    basis=[s**a*x**b*u**c for e in range(2) for c in range(2) for b in range(3) for a in range(2)]
    def numeric(o):
        re=Decimal(0); im=Decimal(0)
        for j,n in enumerate(o['n']):
            q=Decimal(int(n))/Decimal(int(o['d']))*basis[j]
            if j<12: re+=q
            else: im+=q
        return complex(float(re),float(im))
    terms=[(numeric(t['weight']),[(q['word'],numeric(q['coefficient'])) for q in t['polynomial']]) for t in data['terms']]
    mu_float=float(mu)

ck=[sum((1-r/2)*omega**(-k*r) for r in range(5))/5 for k in range(5)]
def random_unitary(n):
    a=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n))
    q,r=np.linalg.qr(a); q=q*(np.diag(r)/np.abs(np.diag(r))).conj()[None,:]
    outcomes=rng.integers(0,5,size=n)
    return (q*omega**outcomes[None,:])@q.conj().T
def lifted(local):
    na=local[0].shape[0]; nb=local[1].shape[0]
    return [np.kron(local[r],np.eye(nb)) if r%2==0 else np.kron(np.eye(na),local[r]) for r in range(4)]
def direct_bell(U):
    n=len(U[0]); B=np.zeros((n,n),complex)
    for r in range(4):
        for k in range(1,5):
            B+=ck[k]*(omega**(-k) if r==3 else 1)*np.linalg.matrix_power(U[r],k)@np.linalg.matrix_power(U[(r+1)%4],-k)
    return B
def wmatrix(w,U):
    M=np.eye(len(U[0]),dtype=complex)
    for r,k in w: M=M@np.linalg.matrix_power(U[r],k)
    return M
def numerical_test(local,label):
    U=lifted(local); B=direct_bell(U); n=len(U[0]); rhs=np.zeros_like(B)
    for weight,poly in terms:
        R=sum((coefficient*wmatrix(w,U) for w,coefficient in poly),np.zeros_like(B))
        rhs+=weight*(R.conj().T@R+R@R.conj().T)
    residual=np.max(np.abs(mu_float*np.eye(n)-B-rhs))
    hermitian=np.max(np.abs(B-B.conj().T))
    maximum=np.linalg.eigvalsh((B+B.conj().T)/2)[-1]
    commutators=[np.linalg.norm(local[0]@local[2]-local[2]@local[0]),np.linalg.norm(local[1]@local[3]-local[3]@local[1])]
    assert residual<1e-10 and hermitian<1e-10 and maximum<=mu_float+1e-10
    return {'label':label,'local_dimensions':[len(local[0]),len(local[1])],
            'maximum_matrix_SOS_residual':float(residual),'Bell_Hermiticity_residual':float(hermitian),
            'maximum_Bell_eigenvalue':float(maximum),'same_party_commutator_Frobenius_norms':list(map(float,commutators))}
matrices=[]
for na,nb in ((2,3),(3,4),(5,5),(5,7),(7,9)):
    local=[random_unitary(na),random_unitary(nb),random_unitary(na),random_unitary(nb)]
    matrices.append(numerical_test(local,'random_PVM'))
# Construct the strategy directly from Fourier vectors in the printed proof.
local=[]
for r in range(4):
    off=(0,.25,.5,-.25)[r]
    columns=np.array([[np.exp(2j*np.pi*j*((a if r%2==0 else -a)+off)/5)/math.sqrt(5) for a in range(5)] for j in range(5)])
    labels=np.arange(5)+(1 if r>=2 else 0)
    local.append((columns*omega**labels[None,:])@columns.conj().T)
matrix_info=numerical_test(local,'printed_attaining_strategy')
U=lifted(local); B=direct_bell(U)
gamma=np.array([numeric(o).real for o in data['gamma']]); psi=np.zeros(25,complex)
for j,g in enumerate(gamma): psi[5*j+j]=g
psi/=np.linalg.norm(psi)
matrix_info['attaining_eigenvector_residual']=float(np.max(np.abs(B@psi-mu_float*psi)))
matrix_info['direct_Bell_expectation']=float(np.vdot(psi,B@psi).real)
assert matrix_info['attaining_eigenvector_residual']<1e-10
matrices.append(matrix_info)
results={'mutation_tests':attacks,'non_load_bearing_parser_issue':schema_issue,'numerical_matrix_spotchecks':matrices,
         'limitations':'Matrix tests use floating point and are falsification probes, not universal proofs. Negative controls reuse supplied checker code and are separate from audit_exact.py.'}
(out/'attack_results.json').write_text(json.dumps(results,indent=2))
print(json.dumps(results,indent=2))
