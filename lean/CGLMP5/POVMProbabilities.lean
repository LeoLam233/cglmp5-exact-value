import CGLMP5.POVMTransfer

noncomputable section
open scoped ComplexOrder
open ContinuousLinearMap

namespace CGLMP5

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Tensor products of arbitrary bounded positive local effects are positive. -/
theorem tensorMap_nonneg {A : Op H} {B : Op K} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ tensorMap A B := by
  have hAp := ContinuousLinearMap.nonneg_iff_isPositive.mp hA
  have hBp := ContinuousLinearMap.nonneg_iff_isPositive.mp hB
  obtain ⟨S, hS, _, hSS⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hAp.isSelfAdjoint hAp.spectrumRestricts
  obtain ⟨T, hT, _, hTT⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hBp.isSelfAdjoint hBp.spectrumRestricts
  have hST : star (tensorMap S T) = tensorMap S T := by
    change (tensorMap S T).adjoint = tensorMap S T
    rw [tensorMap_adjoint]
    change tensorMap (star S) (star T) = _
    rw [hS.star_eq, hT.star_eq]
  rw [← hSS, ← hTT, tensorMap_mul]
  simpa only [hST] using star_mul_self_nonneg (tensorMap S T)

theorem jointProbability_nonneg (φ : State (HTensor H K))
    (A : Setting → POVM H) (B : Setting → POVM K) (x y : Setting) (a b : Outcome) :
    0 ≤ jointProbability φ A B x y a b := by
  have h := φ.functional.map_nonneg (tensorMap_nonneg ((A x).nonneg a) ((B y).nonneg b))
  exact (Complex.le_def.mp h).1

/-- Every setting pair yields total probability one. -/
theorem jointProbability_sum_one (φ : State (HTensor H K))
    (A : Setting → POVM H) (B : Setting → POVM K) (x y : Setting) :
    (∑ a, ∑ b, jointProbability φ A B x y a b) = 1 := by
  have hsum : (∑ a, ∑ b, tensorMap ((A x).effect a) ((B y).effect b)) = 1 := by
    simp only [← tensorMap_sum_right, ← tensorMap_sum_left, (A x).sum_one, (B y).sum_one,
      tensorMap_one]
  calc
    _ = φ.expect (∑ a, ∑ b, tensorMap ((A x).effect a) ((B y).effect b)) := by
      simp [jointProbability, State.expect, map_sum]
    _ = 1 := by rw [hsum, State.expect_one]

end CGLMP5
