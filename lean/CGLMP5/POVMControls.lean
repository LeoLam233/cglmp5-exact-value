import CGLMP5.POVMProbabilities
import Mathlib.Tactic.NormNum

/-! # Exact semantic regression witnesses

These are ordinary kernel-checked counterexamples to unsafe bridge shortcuts.
-/

noncomputable section
open scoped ComplexOrder
open ContinuousLinearMap

namespace CGLMP5

/-- A genuine nonprojective scalar POVM, used to detect compression-as-homomorphism errors. -/
def halfPOVM : POVM ℂ where
  effect a := if a.val < 2 then (1/2 : ℂ) • (1 : Op ℂ) else 0
  nonneg a := by
    split_ifs
    · apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
      exact isPositive_one.smul_of_nonneg (by norm_num [Complex.le_def])
    · exact le_refl 0
  sum_one := by
    simp only [Fin.sum_univ_succ]
    norm_num [← add_smul]

/-- Even this finite scalar POVM has a dilated projection whose compression is not idempotent. -/
theorem compression_not_multiplicative :
    compression (commonJ : ℂ →L[ℂ] DilationSpace ℂ)
        (halfPOVM.dilate.effect 0 * halfPOVM.dilate.effect 0) ≠
      compression commonJ (halfPOVM.dilate.effect 0) *
        compression commonJ (halfPOVM.dilate.effect 0) := by
  rw [halfPOVM.dilate.mul_self]
  simp only [POVM.dilate_compression]
  intro h
  have hv := congrArg (fun T : Op ℂ => T 1) h
  norm_num [halfPOVM, mul_apply_eq_comp] at hv


/-- The fixed inclusion is already a proper isometry for the one-dimensional input space. -/
theorem commonJ_not_surjective :
    ¬ Function.Surjective (commonJ : ℂ →L[ℂ] DilationSpace ℂ) := by
  intro h
  obtain ⟨z,hz⟩ := h (WithLp.toLp 2 (0, PiLp.single 2 (0 : Fin 5) (1 : ℂ)))
  have hv := congrArg (fun p : DilationSpace ℂ => p.snd (0 : Fin 5)) hz
  norm_num [commonJ, sumInl_apply] at hv

/-- V†V=I does not imply VV†=I, even for the explicit fixed embedding in this construction. -/
theorem commonJ_comp_adjoint_ne_one :
    (commonJ : ℂ →L[ℂ] DilationSpace ℂ) ∘L commonJ.adjoint ≠ 1 := by
  intro h
  apply commonJ_not_surjective
  intro y
  refine ⟨commonJ.adjoint y, ?_⟩
  exact congrArg (fun T : Op (DilationSpace ℂ) => T y) h


section EmbeddingControl
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A different, still isometric embedding obtained from a measurement's defect unitary. -/
def rotatedCommonJ (E : POVM H) : H →L[ℂ] DilationSpace H :=
  defectUnitary E.analysis ∘L commonJ

theorem rotatedCommonJ_isometry (E : POVM H) :
    (rotatedCommonJ E).adjoint ∘L rotatedCommonJ E = ContinuousLinearMap.id ℂ H := by
  have hW : defectUnitary E.analysis ∘L defectUnitary E.analysis =
      ContinuousLinearMap.id ℂ (DilationSpace H) := defectUnitary_sq _ E.analysis_isometry
  rw [rotatedCommonJ, adjoint_comp, defectUnitary_adjoint]
  calc
    _ = (commonJ : H →L[ℂ] DilationSpace H).adjoint ∘L
      (defectUnitary E.analysis ∘L defectUnitary E.analysis) ∘L commonJ := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = _ := by rw [hW, id_comp]; exact commonJ_isometry

/-- Changing the embedding changes outcome zero to certainty for the same dilated PVM. -/
theorem rotatedCommonJ_compression_zero (E : POVM H) :
    compression (rotatedCommonJ E) (E.dilate.effect 0) = 1 := by
  have hW (v : DilationSpace H) : defectUnitary E.analysis (defectUnitary E.analysis v) = v :=
    congrArg (fun T : Op (DilationSpace H) => T v) (defectUnitary_sq _ E.analysis_isometry)
  rw [compression_apply, rotatedCommonJ, adjoint_comp, POVM.dilate_effect, defectUnitary_adjoint]
  apply ContinuousLinearMap.ext
  intro h
  simp only [comp_apply, mul_apply_eq_comp, hW]
  simp [commonJ, sumInl_adjoint, commonCoordinate_apply]

end EmbeddingControl

/-- Two valid isometries into the same dilation space need not preserve the same effects. -/
theorem changing_embedding_changes_effect :
    compression (rotatedCommonJ halfPOVM) (halfPOVM.dilate.effect 0) ≠
      compression commonJ (halfPOVM.dilate.effect 0) := by
  rw [rotatedCommonJ_compression_zero, POVM.dilate_compression]
  intro h
  have hv := congrArg (fun T : Op ℂ => T 1) h
  norm_num [halfPOVM] at hv

end CGLMP5
