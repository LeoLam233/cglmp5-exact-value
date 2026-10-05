#!/usr/bin/env python3
"""Full25D matrix Bell action:125 diagonal-input column entries, never merely compression."""
from pathlib import Path
import sympy as S
J,U,R=S.symbols('J U R');gens=[J*J+1,U*U-10-2*R,R*R-5]
def red(p):return S.reduced(S.expand(p),gens,J,U,R)[1]
z=(U+J*(R-1))/4;ps=[red(z**k) for k in range(20)]
def lean(p):return str(S.expand(p)).replace('**','^').replace('J','Complex.I').replace('R','(s : ℂ)').replace('U','(u : ℂ)')
def cert(p):
 qs,r=S.reduced(S.expand(p),gens,J,U,R);assert r==0,r
 return ' + '.join(f'({lean(q)}) * {h}' for q,h in zip(qs,['hI','hu','hs']) if q!=0) or '0 * hs'
cs=[red(sum(S.Rational(2-t,10)*ps[-4*k*t%20] for t in range(5))) for k in range(1,5)]
out='''import CGLMP5.AttainmentBellDefs
namespace CGLMP5.Attainment
noncomputable section

def coefficientTable : Fin 4 → ℂ :=
  !['''+',\n    '.join(lean(c) for c in cs)+''']

lemma omega_pow_phase (k : ℕ) : (zeta^4)^k = phase (4*k) := by
  rw [← pow_mul, phase_eq_pow]

lemma coefficientTable_eq (k : Fin 4) : SOS.fourierCoeff (zeta^4) (k.val+1) = coefficientTable k := by
  have hs : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
  have hu : (u : ℂ)^2 = 10 + 2*(s : ℂ) := by exact_mod_cast u_sq
  have hI := Complex.I_sq
  simp only [SOS.fourierCoeff, omega_pow_phase]
  fin_cases k
'''
for k in range(1,5):
 p=sum(S.Rational(2-t,10)*ps[-4*k*t%20] for t in range(5))-cs[k-1]
 out+='  · norm_num [phase, phaseTable, coefficientTable, Fin.sum_univ_succ]\n    all_goals linear_combination (norm := (ring_nf; simp [Complex.I_sq, Complex.I_pow_three]; ring)) '+cert(p)+'\n'
out+='end\nend CGLMP5.Attainment\n';Path('CGLMP5/AttainmentCoefficient.lean').write_text(out)

def step(r,j):
 return ((j+(-1 if r%2==0 else 1))%5,[0,(16 if j==4 else 1),(12 if j==0 else 2),(8 if j==4 else 3)][r])
def it(r,k,j):
 e=0
 for _ in range(k):j,a=step(r,j);e+=a
 return j,e
for l in range(5):
 o=f'''import CGLMP5.AttainmentCoefficient
namespace CGLMP5.Attainment
noncomputable section
set_option maxHeartbeats 1600000 in
/-- All25 output coordinates for input |{l}{l}>, including20 off-diagonal zeros. -/
lemma matrixBell_column_{l} (i j : Fin 5) : matrixBell (i,j) ({l},{l}) =
    if i = j then toeplitzEntry i {l} else 0 := by
  have hs : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
  have hu : (u : ℂ)^2 = 10 + 2*(s : ℂ) := by exact_mod_cast u_sq
  have hI := Complex.I_sq
  simp only [matrixBell, SOS.edgeCoefficient, coefficientTable_eq, omega_pow_phase]
  fin_cases i <;> fin_cases j
'''
 for i in range(5):
  for j in range(5):
   poly=0
   for r in range(4):
    for k in range(1,5):
     ar,ak,br,bk=[(0,k,1,5-k),(2,5-k,1,k),(2,k,3,5-k),(0,5-k,3,k)][r]
     ai,ae=it(ar,ak,l);bi,be=it(br,bk,l)
     if ai==i and bi==j:poly+=cs[k-1]*(ps[-4*k%20] if r==3 else 1)*ps[ae%20]*ps[be%20]
   fs=[0,U*(5-R)/20,(R-1)/2,U*R/10,(R+1)/2]
   if i==j:poly-=fs[abs(i-l)]
   o+='  · norm_num [edgeMatrix, stepMatrix_pow, Matrix.kroneckerMap_apply, Matrix.of_apply,\n      stepIter, phaseIter, stepDest, stepPhase, phase, phaseTable, coefficientTable,\n      toeplitzEntry, distanceIndex, Fin.sum_univ_succ]\n    all_goals linear_combination (norm := (ring_nf; simp [Complex.I_sq, Complex.I_pow_three]; ring)) '+cert(poly)+'\n'
 o+='end\nend CGLMP5.Attainment\n';Path(f'CGLMP5/AttainmentColumn{l}.lean').write_text(o)
