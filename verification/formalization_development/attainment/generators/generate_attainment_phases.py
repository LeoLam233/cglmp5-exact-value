#!/usr/bin/env python3
"""Generate explicit kernel-checkable 20th-root table recurrence certificates."""
from pathlib import Path
import sympy as S
J,U,R=S.symbols('J U R')
gens=[J*J+1,U*U-10-2*R,R*R-5]
def reduce(p): return S.reduced(S.expand(p),gens,J,U,R)[1]
z=(U+J*(R-1))/4
ps=[reduce(z**k) for k in range(20)]
def lean(p): return str(S.expand(p)).replace('**','^').replace('J','Complex.I')
def cert(p):
 qs,r=S.reduced(S.expand(p),gens,J,U,R);assert r==0
 return ' + '.join(f'({lean(q)}) * {h}' for q,h in zip(qs,['hI','hu','hs']) if q!=0) or '0 * hs'
o='''import CGLMP5.Root
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Omega

namespace CGLMP5.Attainment
noncomputable section
open Complex

/-- A complete algebraic table for exp(k*pi*i/10), with no numerical entries. -/
def phaseTable (R U : ℂ) : Fin 20 → ℂ :=
  !['''+',\n    '.join(lean(p) for p in ps)+''']

theorem phaseTable_step (R U : ℂ) (hs : R^2 = 5) (hu : U^2 = 10 + 2*R)
    (k : Fin 20) :
    phaseTable R U ⟨(k.val+1)%20, Nat.mod_lt _ (by omega)⟩ =
      phaseTable R U k * ((U + Complex.I*(R-1))/4) := by
  have hI := Complex.I_sq
  fin_cases k
'''
for k in range(20):
 p=ps[(k+1)%20]-ps[k]*z
 o+=f'  · change ({lean(ps[(k+1)%20])}) = ({lean(ps[k])}) * ((U + Complex.I*(R-1))/4)\n    linear_combination {cert(p)}\n'
o+='''
def phase (n : ℕ) : ℂ := phaseTable (s : ℂ) (u : ℂ) ⟨n % 20, Nat.mod_lt _ (by omega)⟩

lemma phase_succ (n : ℕ) : phase (n+1) = phase n * zeta := by
  have hs : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
  have hu : (u : ℂ)^2 = 10 + 2*(s : ℂ) := by exact_mod_cast u_sq
  have h := phaseTable_step (s : ℂ) (u : ℂ) hs hu ⟨n%20, Nat.mod_lt _ (by omega)⟩
  simpa [phase, zeta, Nat.add_mod] using h

lemma phase_eq_pow (n : ℕ) : phase n = zeta^n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [phase_succ, ih, pow_succ]

lemma zeta_pow_twenty : zeta^20 = 1 := by
  rw [← phase_eq_pow]
  norm_num [phase, phaseTable]

lemma phase_mod (n : ℕ) : phase (n%20) = phase n := by
  simp [phase]

lemma phase_add (n m : ℕ) : phase (n+m) = phase n * phase m := by
  simp only [phase_eq_pow, pow_add]

lemma phase_zero : phase 0 = 1 := by rfl
lemma phase_five : phase 5 = Complex.I := by norm_num [phase, phaseTable]

end
end CGLMP5.Attainment
'''
Path('CGLMP5/AttainmentPhases.lean').write_text(o)
