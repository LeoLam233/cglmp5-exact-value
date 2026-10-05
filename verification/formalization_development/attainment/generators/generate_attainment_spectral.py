#!/usr/bin/env python3
"""Generate100 Fourier-projector/spectral-unitary identities in four shards."""
from pathlib import Path
import sympy as S
J,U,R=S.symbols('J U R');gens=[J*J+1,U*U-10-2*R,R*R-5]
def red(p):return S.reduced(S.expand(p),gens,J,U,R)[1]
z=(U+J*(R-1))/4;ps=[red(z**k) for k in range(20)]
def lean(p):return str(S.expand(p)).replace('**','^').replace('J','Complex.I').replace('R','(s : ℂ)').replace('U','(u : ℂ)')
def cert(p):
 qs,r=S.reduced(S.expand(p),gens,J,U,R);assert r==0,r
 return ' + '.join(f'({lean(q)}) * {h}' for q,h in zip(qs,['hI','hu','hs']) if q!=0) or '0 * hs'
def ex(r,a,j):return [4*a,21-4*a,4*a+2,19-4*a][r]*j
for r in range(4):
 o=f'''import CGLMP5.AttainmentMatrixDefs
namespace CGLMP5.Attainment
noncomputable section
set_option maxHeartbeats 1200000 in
/-- Exact25-entry Fourier/spectral bridge for measurement r={r}. -/
lemma localSpectral_step_{r} : localSpectral {r} = stepMatrix {r} := by
  have hs : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
  have hu : (u : ℂ)^2 = 10 + 2*(s : ℂ) := by exact_mod_cast u_sq
  have hI := Complex.I_sq
  ext i j
  fin_cases i <;> fin_cases j
'''
 for i in range(5):
  for j in range(5):
   dst=(j+(-1 if r%2==0 else 1))%5
   p=[0,(16 if j==4 else 1),(12 if j==0 else 2),(8 if j==4 else 3)][r]
   poly=sum(ps[(4*(a+(r>=2)))%20]*ps[ex(r,a,i)%20]*ps[-ex(r,a,j)%20]/5 for a in range(5))-(ps[p] if i==dst else 0)
   o+='  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,\n      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]\n    all_goals linear_combination '+cert(poly)+'\n'
 o+='end\nend CGLMP5.Attainment\n'
 Path(f'CGLMP5/AttainmentSpectral{r}.lean').write_text(o)
