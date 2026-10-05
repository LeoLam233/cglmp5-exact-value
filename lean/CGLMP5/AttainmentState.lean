import CGLMP5.Root
import CGLMP5.AttainmentAlgebra
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace CGLMP5.Attainment
noncomputable section
open scoped BigOperators

/-- The actual two nontrivial positive Schmidt amplitudes. -/
def schmidtA : ℝ := coeffA mu s u
def schmidtB : ℝ := coeffB mu s

def gamma : Fin 5 → ℝ := ![1, schmidtA, schmidtB, schmidtA, 1]

def normSq : ℝ := 2 + 2*schmidtA^2 + schmidtB^2

lemma schmidtA_pos : 0 < schmidtA :=
  coeffA_pos mu s u s_sq u_sq mu_cubic s_pos u_pos mu_gt_three
lemma schmidtB_pos : 0 < schmidtB :=
  coeffB_pos mu s u s_sq u_sq mu_cubic s_pos u_pos mu_gt_three
lemma normSq_pos : 0 < normSq := by unfold normSq; positivity
lemma gamma_pos (j : Fin 5) : 0 < gamma j := by
  fin_cases j <;> simp [gamma, schmidtA_pos, schmidtB_pos]

/-- The full 25-dimensional unnormalized Schmidt state, with all20 off-diagonal coordinates zero. -/
def rawState : EuclideanSpace ℂ (Fin 5 × Fin 5) :=
  WithLp.toLp 2 (fun ij => if ij.1 = ij.2 then (gamma ij.1 : ℂ) else 0)

/-- The physical unit vector on C^5 tensor C^5, in product-basis coordinates. -/
def state : EuclideanSpace ℂ (Fin 5 × Fin 5) :=
  ((Real.sqrt normSq : ℂ)⁻¹) • rawState

lemma rawState_apply (i j : Fin 5) : rawState (i,j) =
    if i = j then (gamma i : ℂ) else 0 := rfl

lemma rawState_norm_sq : ‖rawState‖^2 = normSq := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [rawState, Fintype.sum_prod_type, gamma, Fin.sum_univ_succ,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, normSq]
  <;> ring

lemma rawState_norm : ‖rawState‖ = Real.sqrt normSq := by
  have hp := normSq_pos
  have hs := Real.sq_sqrt (le_of_lt hp)
  nlinarith [rawState_norm_sq, norm_nonneg rawState, Real.sqrt_nonneg normSq]

lemma state_norm : ‖state‖ = 1 := by
  have hs : 0 < Real.sqrt normSq := Real.sqrt_pos.2 normSq_pos
  simp [state, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs, rawState_norm, ne_of_gt hs]

lemma state_apply (i j : Fin 5) : state (i,j) =
    if i = j then (gamma i : ℂ) / (Real.sqrt normSq : ℂ) else 0 := by
  simp [state, rawState, div_eq_mul_inv, mul_comm]

/-- The20 off-diagonal coordinates vanish in the full physical Hilbert space. -/
lemma state_off_diagonal (i j : Fin 5) (h : i ≠ j) : state (i,j) = 0 := by
  simp [state_apply, h]

end
end CGLMP5.Attainment
