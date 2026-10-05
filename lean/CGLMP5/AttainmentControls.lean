import CGLMP5.Attainment

namespace CGLMP5.Attainment.Controls
noncomputable section
open scoped BigOperators Matrix

/-- Leakage invisible to the five-dimensional diagonal compression. -/
def leakMatrix : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ :=
  Matrix.of (fun i j => if i = (0,1) ∧ j = (0,0) then 1 else 0)

def badBell := matrixBell + leakMatrix

lemma leak_diagonal (i j : Fin 5) : leakMatrix (i,i) (j,j) = 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [leakMatrix]

lemma badBell_same_compression (i j : Fin 5) : badBell (i,i) (j,j) = matrixBell (i,i) (j,j) := by
  simp [badBell, Matrix.add_apply, leak_diagonal]

lemma leak_mulVec (v : (Fin 5 × Fin 5) → ℂ) : (leakMatrix *ᵥ v) (0,1) = v (0,0) := by
  simp [Matrix.mulVec, dotProduct, leakMatrix]

lemma state_zerozero : state (0,0) = (Real.sqrt normSq : ℂ)⁻¹ := by
  simp [state_apply, gamma]

lemma state_zerozero_ne : state (0,0) ≠ 0 := by
  rw [state_zerozero]
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 normSq_pos)))

lemma badBell_offdiagonal_output : (matrixOp badBell state) (0,1) = state (0,0) := by
  have h := congrArg (fun v : H25 => v (0,1)) state_eigen
  change (matrixBell *ᵥ WithLp.ofLp state) (0,1) = (mu : ℂ) * state (0,1) at h
  have hz : state (0,1) = 0 := state_off_diagonal 0 1 (by decide)
  change ((matrixBell + leakMatrix) *ᵥ WithLp.ofLp state) (0,1) = _
  rw [Matrix.add_mulVec]
  simp only [Pi.add_apply, h, hz, mul_zero, zero_add, leak_mulVec]

/-- Equality of compressed matrices is insufficient for the full physical eigen-equation. -/
lemma compression_surrogate_rejected : matrixOp badBell state ≠ (mu : ℂ) • state := by
  intro h
  have hc := congrArg (fun v : H25 => v (0,1)) h
  rw [badBell_offdiagonal_output] at hc
  have hz : state (0,1) = 0 := state_off_diagonal 0 1 (by decide)
  change state (0,0) = (mu : ℂ) * state (0,1) at hc
  rw [hz, mul_zero] at hc
  exact state_zerozero_ne hc

/-- Bob's beta0 is deliberately corrupted from1/4 to0. -/
def wrongBobMatrix (a : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => phase ((20-4*a.val)*i.val) * star (phase ((20-4*a.val)*j.val)) / 5

def wrongBobSpectral : Matrix (Fin 5) (Fin 5) ℂ :=
  ∑ a : Fin 5, phase (4*a.val) • wrongBobMatrix a

lemma wrongBob_entry : wrongBobSpectral 1 0 = 1 := by
  have hh (a : Fin 5) : phase (4*a.val) * phase (20-4*a.val) = 1 := by
    rw [← phase_add]
    have he : 4*a.val+(20-4*a.val) = 20 := by omega
    rw [he]
    norm_num [phase, phaseTable]
  simp only [wrongBobSpectral, Matrix.sum_apply, Matrix.smul_apply, wrongBobMatrix,
    Fin.val_zero, Fin.val_one, mul_zero, phase_zero, star_one, mul_one, smul_eq_mul]
  simp_rw [← mul_div_assoc, hh]
  norm_num

lemma phase_one_ne_one : phase 1 ≠ 1 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num [phase, phaseTable] at hi
  linarith [s_gt_two]

lemma wrong_offset_rejected : wrongBobSpectral ≠ localSpectral 1 := by
  intro h
  have hi := congrArg (fun A : Matrix (Fin 5) (Fin 5) ℂ => A 1 0) h
  rw [wrongBob_entry, localSpectral_step] at hi
  norm_num [stepMatrix, stepDest, stepPhase] at hi
  exact phase_one_ne_one hi.symm

/-- Corrupt the middle Schmidt amplitude by+1, then genuinely renormalize. -/
def corruptRaw : H25 := rawState + EuclideanSpace.single (2,2) 1

def corruptState : H25 := ((‖corruptRaw‖ : ℂ)⁻¹) • corruptRaw

lemma corruptRaw_nonzero : corruptRaw ≠ 0 := by
  intro h
  have hi := congrArg (fun v : H25 => v (0,0)) h
  norm_num [corruptRaw, rawState, gamma, EuclideanSpace.single_apply] at hi

lemma corruptState_norm : ‖corruptState‖ = 1 := by
  have hn : ‖corruptRaw‖ ≠ 0 := norm_ne_zero_iff.mpr corruptRaw_nonzero
  simp [corruptState, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg corruptRaw), hn]

lemma corrupt_center_residual : (matrixOp matrixBell corruptRaw) (2,2) -
    (mu : ℂ) * corruptRaw (2,2) = -(mu : ℂ) := by
  have hr := congrArg (fun v : H25 => v (2,2)) rawState_eigen
  have hc : matrixOp matrixBell (EuclideanSpace.single (2,2) 1) (2,2) = 0 := by
    rw [matrixOperator_single, matrixBell_diagonal_2]
    norm_num [toeplitzEntry, distanceIndex]
  simp only [corruptRaw, map_add, PiLp.add_apply, hc]
  change (matrixOp matrixBell rawState) (2,2) = (mu : ℂ) * rawState (2,2) at hr
  rw [hr]
  simp [EuclideanSpace.single_apply]
  <;> ring

lemma corruptRaw_not_eigen : matrixOp matrixBell corruptRaw ≠ (mu : ℂ) • corruptRaw := by
  intro h
  have hc := congrArg (fun v : H25 => v (2,2)) h
  have he := corrupt_center_residual
  change (matrixOp matrixBell corruptRaw) (2,2) = (mu : ℂ) * corruptRaw (2,2) at hc
  rw [hc, sub_self] at he
  have hm : (mu : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans (by norm_num) mu_gt_three))
  exact hm (neg_eq_zero.mp he.symm)

/-- Normalization cannot repair the corrupted Schmidt eigenvector. -/
lemma normalized_schmidt_rejected : matrixOp matrixBell corruptState ≠ (mu : ℂ) • corruptState := by
  intro h
  have hn : (‖corruptRaw‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr corruptRaw_nonzero)
  apply corruptRaw_not_eigen
  simp only [corruptState, map_smul] at h
  rw [smul_comm (mu : ℂ)] at h
  have hh := congrArg (fun v : H25 => (‖corruptRaw‖ : ℂ) • v) h
  simpa only [smul_smul, ← mul_assoc, mul_inv_cancel₀ hn, one_mul, one_smul] using hh

end
end CGLMP5.Attainment.Controls
