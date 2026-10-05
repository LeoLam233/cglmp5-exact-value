#!/usr/bin/env python3
"""Fourier PVM finite proofs with explicit ring certificates, checked by Lean."""
from pathlib import Path
import sympy as S
J,U,R=S.symbols('J U R');gens=[J*J+1,U*U-10-2*R,R*R-5]
def red(p):return S.reduced(S.expand(p),gens,J,U,R)[1]
z=(U+J*(R-1))/4;ps=[red(z**k) for k in range(20)]
def lean(p):return str(S.expand(p)).replace('**','^').replace('J','Complex.I').replace('R','(s : ℂ)').replace('U','(u : ℂ)')
def cert(p):
 qs,r=S.reduced(S.expand(p),gens,J,U,R);assert r==0
 return ' + '.join(f'({lean(q)}) * {h}' for q,h in zip(qs,['hI','hu','hs']) if q!=0) or '0 * hs'
def ex(r,a,j):return [4*a,21-4*a,4*a+2,19-4*a][r]*j
out='''import CGLMP5.AttainmentPhases
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace CGLMP5.Attainment
noncomputable section
open scoped BigOperators

/-- r=0,2 are Alice settings0,1; r=1,3 are Bob settings0,1.
The exponents are exactly j*(4a+2x) and j*(-4b+1-2y), modulo20. -/
def phaseExponent (r : Fin 4) (a j : Fin 5) : ℕ :=
  (![4*a.val, 21-4*a.val, 4*a.val+2, 19-4*a.val] r) * j.val

def fourierVector (r : Fin 4) (a : Fin 5) : EuclideanSpace ℂ (Fin 5) :=
  WithLp.toLp 2 (fun j => (s : ℂ) / 5 * phase (phaseExponent r a j))

/-- Exact cancellation of fifth roots of unity, for all four actual offset choices. -/
lemma phase_overlap (r : Fin 4) (a b : Fin 5) :
    (∑ j : Fin 5, star (phase (phaseExponent r a j)) * phase (phaseExponent r b j)) =
      if a = b then (5 : ℂ) else 0 := by
  have hs : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
  have hu : (u : ℂ)^2 = 10 + 2*(s : ℂ) := by exact_mod_cast u_sq
  have hI := Complex.I_sq
  simp only [star_phase]
  fin_cases r <;> fin_cases a <;> fin_cases b
'''
for r in range(4):
 for a in range(5):
  for b in range(5):
   poly=sum(ps[-ex(r,a,j)%20]*ps[ex(r,b,j)%20] for j in range(5))-(5 if a==b else 0)
   out+='  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]\n    all_goals linear_combination '+cert(poly)+'\n'
out+='''
end
end CGLMP5.Attainment
'''
Path('CGLMP5/AttainmentFourier.lean').write_text(out)
