import CGLMP5.SOSDefinitions
import CGLMP5.Events
import CGLMP5.Spectral
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace CGLMP5

/-- The actual root-of-unity relation suffices; no numerical Fourier check is used. -/
theorem fourier_synthesis (ω : ℂ) (hω : ω^5=1)
    (hc : 1+ω+ω^2+ω^3+ω^4=0) (z : Fin 5) :
    (∑ k : Fin 4, SOS.fourierCoeff ω (k.val+1) * ω^(((k.val+1)*z.val)%5)) =
      (2-(z.val:ℂ))/2 := by
  have h6 : ω^6=ω := by simpa using pow_eq_pow_mod 6 hω
  have h7 : ω^7=ω^2 := by simpa using pow_eq_pow_mod 7 hω
  have h8 : ω^8=ω^3 := by simpa using pow_eq_pow_mod 8 hω
  fin_cases z <;>
    norm_num [SOS.fourierCoeff, Fin.sum_univ_succ] <;>
    ring_nf
  all_goals
    try simp only [hω, h6, h7, h8]
    try norm_num
  all_goals solve
    | linear_combination (-1/5:ℂ) * hc
    | linear_combination (-1/10:ℂ) * hc
    | ring
    | linear_combination (1/10:ℂ) * hc
    | linear_combination (1/5:ℂ) * hc

/-- Integer residue arithmetic for each Fourier exponent and outcome pair. -/
theorem pair_exponent_mod : ∀ (a b : Fin 5) (shift : Fin 2) (j : Fin 4),
    (a.val*(j.val+1) + b.val*(5-(j.val+1)) +
       ((5-((j.val+1)*shift.val)%5)%5))%5 =
      ((j.val+1)*((a.val+10-b.val-shift.val)%5))%5 := by decide

theorem scalar_pair_fourier (ω : ℂ) (hω : ω^5=1)
    (hc : 1+ω+ω^2+ω^3+ω^4=0) (a b : Fin 5) (shift : Fin 2) :
    (∑ j : Fin 4, (SOS.fourierCoeff ω (j.val+1) * ω^((5-((j.val+1)*shift.val)%5)%5)) *
      ((ω^a.val)^(j.val+1) * (ω^b.val)^(5-(j.val+1)))) =
      (2-(↑((a.val+10-b.val-shift.val)%5):ℂ))/2 := by
  have he (j : Fin 4) :
      ω^((5-((j.val+1)*shift.val)%5)%5) *
        ((ω^a.val)^(j.val+1) * (ω^b.val)^(5-(j.val+1))) =
      ω^(((j.val+1)*((a.val+10-b.val-shift.val)%5))%5) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    rw [mul_comm, ← pow_add, pow_eq_pow_mod _ hω, pair_exponent_mod]
  simp_rw [mul_assoc, he]
  exact fourier_synthesis ω hω hc ⟨(a.val+10-b.val-shift.val)%5, Nat.mod_lt _ (by decide)⟩

/-- The outcome-label permutation a ↦ a−1 modulo five. -/
def shiftDown : Fin 5 ≃ Fin 5 where
  toFun a := ⟨(a.val+4)%5, Nat.mod_lt _ (by decide)⟩
  invFun a := ⟨(a.val+1)%5, Nat.mod_lt _ (by decide)⟩
  left_inv := by decide
  right_inv := by decide

section Operators
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

noncomputable def pairBell (ω : ℂ) (P Q : PVM R) (shift : Fin 2) : R :=
  ∑ j : Fin 4, (SOS.fourierCoeff ω (j.val+1) * ω^((5-((j.val+1)*shift.val)%5)%5)) •
    ((P.phase ω)^(j.val+1) * (Q.phase ω)^(5-(j.val+1)))

/-- Fourier inversion inside any complex star algebra, with preserved product order. -/
theorem pairBell_eq (ω : ℂ) (hω : ω^5=1)
    (hc : 1+ω+ω^2+ω^3+ω^4=0) (P Q : PVM R) (shift : Fin 2) :
    pairBell ω P Q shift =
      ∑ a : Fin 5, ∑ b : Fin 5, ((2-(↑((a.val+10-b.val-shift.val)%5):ℂ))/2) •
        (P.effect a * Q.effect b) := by
  unfold pairBell
  simp_rw [PVM.phase, PVM.eval_pow, PVM.eval_mul_eval, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_smul, scalar_pair_fourier ω hω hc]

/-- Reindexing both measurements preserves the original outcome labels in the conclusion. -/
theorem pairBell_reindex (ω : ℂ) (hω : ω^5=1)
    (hc : 1+ω+ω^2+ω^3+ω^4=0) (P Q : PVM R) (e f : Fin 5 ≃ Fin 5)
    (shift : Fin 2) :
    pairBell ω (P.reindex e) (Q.reindex f) shift =
      ∑ a : Fin 5, ∑ b : Fin 5,
        ((2-(↑(((e.symm a).val+10-(f.symm b).val-shift.val)%5):ℂ))/2) •
          (P.effect a * Q.effect b) := by
  rw [pairBell_eq ω hω hc]
  symm
  calc
    _ = ∑ a : Fin 5, ∑ b : Fin 5,
        ((2-(↑(((e.symm (e a)).val+10-(f.symm b).val-shift.val)%5):ℂ))/2) •
          (P.effect (e a) * Q.effect b) := (e.sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← f.sum_comp]
      simp only [Equiv.symm_apply_apply, PVM.reindex]


end Operators
end CGLMP5
