import CGLMP5.AttainmentMatrixDefs
namespace CGLMP5.Attainment
noncomputable section
set_option maxHeartbeats 1200000 in
/-- Exact25-entry Fourier/spectral bridge for measurement r=1. -/
lemma localSpectral_step_1 : localSpectral 1 = stepMatrix 1 := by
  have hs : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
  have hu : (u : ℂ)^2 = 10 + 2*(s : ℂ) := by exact_mod_cast u_sq
  have hI := Complex.I_sq
  ext i j
  fin_cases i <;> fin_cases j
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) 0 * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) ((s : ℂ)^2*(u : ℂ)/80 + (u : ℂ)/16) * hI + (-Complex.I*(s : ℂ)^2/320 + 3*Complex.I*(s : ℂ)/160 - Complex.I/64) * hu + (-Complex.I*(s : ℂ)/160 + 3*Complex.I/160) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-(s : ℂ)^2*(u : ℂ)^2/320 + (u : ℂ)^2/64) * hI + ((s : ℂ)^2/320 - 1/64) * hu + (-3*Complex.I*(u : ℂ)/160 + (s : ℂ)/160 + 3/160) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) ((s : ℂ)^2*(u : ℂ)/80 - (u : ℂ)/16) * hI + (Complex.I*(s : ℂ)^2/320 - Complex.I/64) * hu + (Complex.I*(s : ℂ)/160 + 7*Complex.I/160 - (u : ℂ)/160) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) ((s : ℂ)^2*(u : ℂ)^2/320 - 3*(s : ℂ)*(u : ℂ)^2/160 + (u : ℂ)^2/64) * hI + (-(s : ℂ)^2/320 + 3*(s : ℂ)/160 - 1/64) * hu + (-Complex.I*(u : ℂ)/40 - (s : ℂ)/160 - 1/160) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-(s : ℂ)^2*(u : ℂ)/80 - (u : ℂ)/16) * hI + (-Complex.I*(s : ℂ)^2/320 + 3*Complex.I*(s : ℂ)/160 - Complex.I/64) * hu + (-Complex.I*(s : ℂ)/160 - Complex.I/160 + (u : ℂ)/40) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-3*Complex.I*(s : ℂ)^2*(u : ℂ)/320 + 3*Complex.I*(u : ℂ)/64 + (s : ℂ)^3/320 - 3*(s : ℂ)^2/320 - (s : ℂ)/64 + 3/64) * hI + (Complex.I*(s : ℂ)^3*(u : ℂ)/2560 - Complex.I*(s : ℂ)^2*(u : ℂ)/2560 - Complex.I*(s : ℂ)*(u : ℂ)/512 + Complex.I*(u : ℂ)/512 - (s : ℂ)^2/640 + 1/128) * hu + (Complex.I*(s : ℂ)^2*(u : ℂ)/1280 + Complex.I*(s : ℂ)*(u : ℂ)/320 + 7*Complex.I*(u : ℂ)/1280 - (s : ℂ)/160 - 1/160) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^3*(u : ℂ)^2/1280 + Complex.I*(s : ℂ)^2*(u : ℂ)^2/256 - 7*Complex.I*(s : ℂ)*(u : ℂ)^2/1280 - Complex.I*(u : ℂ)^2/256 - (s : ℂ)^3*(u : ℂ)/640 + (s : ℂ)^2*(u : ℂ)^3/640 - (s : ℂ)^2*(u : ℂ)/128 - (s : ℂ)*(u : ℂ)^3/640 + (s : ℂ)*(u : ℂ)/128 + 5*(u : ℂ)/128) * hI + (Complex.I*(s : ℂ)^3/640 - 3*Complex.I*(s : ℂ)^2/640 + Complex.I*(s : ℂ)/640 + Complex.I/128 - (s : ℂ)^2*(u : ℂ)/640 + (s : ℂ)*(u : ℂ)/640) * hu + (Complex.I*(s : ℂ)^2/320 + Complex.I*(s : ℂ)/320 - Complex.I/40 - 3*(s : ℂ)*(u : ℂ)/640 + 3*(u : ℂ)/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^2*(u : ℂ)/320 - 3*Complex.I*(u : ℂ)/64 + (s : ℂ)^3/320 - (s : ℂ)^2*(u : ℂ)^2/640 - (s : ℂ)^2/320 + 3*(s : ℂ)/64 + (u : ℂ)^2/128 - 3/64) * hI + (-Complex.I*(s : ℂ)^2*(u : ℂ)/640 + Complex.I*(s : ℂ)*(u : ℂ)/640 + 3*(s : ℂ)/320 - 1/64) * hu + (Complex.I*(s : ℂ)*(u : ℂ)/640 - Complex.I*(u : ℂ)/128 - (s : ℂ)/320 + 7/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^3*(u : ℂ)^2/1280 + Complex.I*(s : ℂ)^2*(u : ℂ)^2/1280 + Complex.I*(s : ℂ)*(u : ℂ)^2/256 - Complex.I*(u : ℂ)^2/256 - (s : ℂ)^3*(u : ℂ)^3/2560 + (s : ℂ)^3*(u : ℂ)/320 + (s : ℂ)^2*(u : ℂ)^3/2560 + (s : ℂ)^2*(u : ℂ)/160 + (s : ℂ)*(u : ℂ)^3/512 - (s : ℂ)*(u : ℂ)/64 - (u : ℂ)^3/512 - (u : ℂ)/32) * hI + (Complex.I*(s : ℂ)^3/640 - Complex.I*(s : ℂ)/128 + (s : ℂ)^3*(u : ℂ)/2560 - (s : ℂ)^2*(u : ℂ)/2560 - (s : ℂ)*(u : ℂ)/512 + (u : ℂ)/512) * hu + (Complex.I*(s : ℂ)^2/320 + Complex.I*(s : ℂ)/80 + 3*Complex.I/320 + (s : ℂ)^2*(u : ℂ)/1280 - (s : ℂ)*(u : ℂ)/320 - 9*(u : ℂ)/1280) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) ((s : ℂ)^2*(u : ℂ)^2/320 - (u : ℂ)^2/64) * hI + (1/64 - (s : ℂ)^2/320) * hu + (-Complex.I*(u : ℂ)/160 - (s : ℂ)/160 - 7/160) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^3*(u : ℂ)^2/1280 + Complex.I*(s : ℂ)^2*(u : ℂ)^2/256 - 7*Complex.I*(s : ℂ)*(u : ℂ)^2/1280 - Complex.I*(u : ℂ)^2/256 - (s : ℂ)^3*(u : ℂ)/640 - (s : ℂ)^2*(u : ℂ)^3/640 - 9*(s : ℂ)^2*(u : ℂ)/640 + (s : ℂ)*(u : ℂ)^3/640 + (s : ℂ)*(u : ℂ)/128 - 7*(u : ℂ)/128) * hI + (Complex.I*(s : ℂ)^3/640 - Complex.I*(s : ℂ)^2/128 + 13*Complex.I*(s : ℂ)/640 - Complex.I/128 + (s : ℂ)^2*(u : ℂ)/640 - (s : ℂ)*(u : ℂ)/640) * hu + (Complex.I*(s : ℂ)^2/320 + Complex.I*(s : ℂ)/320 - Complex.I/40 + (s : ℂ)*(u : ℂ)/640 + 23*(u : ℂ)/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (Complex.I*(s : ℂ)^3*(u : ℂ)^3/2560 - 3*Complex.I*(s : ℂ)^2*(u : ℂ)^3/2560 - Complex.I*(s : ℂ)*(u : ℂ)^3/2560 - Complex.I*(u : ℂ)^3/512 + (s : ℂ)^3*(u : ℂ)^2/1280 - (s : ℂ)^2*(u : ℂ)^2/256 + 7*(s : ℂ)*(u : ℂ)^2/1280 + (u : ℂ)^2/256) * hI + (-Complex.I*(s : ℂ)^3*(u : ℂ)/2560 + 3*Complex.I*(s : ℂ)^2*(u : ℂ)/2560 + Complex.I*(s : ℂ)*(u : ℂ)/2560 + Complex.I*(u : ℂ)/512 - (s : ℂ)^3/1280 + (s : ℂ)^2/256 - 7*(s : ℂ)/1280 - 1/256) * hu + (-Complex.I*(s : ℂ)^2*(u : ℂ)/1280 - Complex.I*(s : ℂ)*(u : ℂ)/640 + 7*Complex.I*(u : ℂ)/1280 - (s : ℂ)^2/640 - (s : ℂ)/320 + 11/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^3*(u : ℂ)^2/1280 + 3*Complex.I*(s : ℂ)^2*(u : ℂ)^2/1280 - 7*Complex.I*(s : ℂ)*(u : ℂ)^2/1280 + Complex.I*(u : ℂ)^2/256 - (s : ℂ)^3*(u : ℂ)^3/2560 - (s : ℂ)^3*(u : ℂ)/640 + 3*(s : ℂ)^2*(u : ℂ)^3/2560 - 7*(s : ℂ)^2*(u : ℂ)/640 + (s : ℂ)*(u : ℂ)^3/2560 + (s : ℂ)*(u : ℂ)/128 + (u : ℂ)^3/512 + 7*(u : ℂ)/128) * hI + (Complex.I*(s : ℂ)^3/1280 - Complex.I*(s : ℂ)^2/1280 + 7*Complex.I*(s : ℂ)/1280 - 3*Complex.I/256 + (s : ℂ)^3*(u : ℂ)/2560 - 3*(s : ℂ)^2*(u : ℂ)/2560 - (s : ℂ)*(u : ℂ)/2560 - (u : ℂ)/512) * hu + (Complex.I*(s : ℂ)^2/640 + 3*Complex.I*(s : ℂ)/320 + 9*Complex.I/640 + (s : ℂ)^2*(u : ℂ)/1280 + 3*(s : ℂ)*(u : ℂ)/640 + 21*(u : ℂ)/1280) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (Complex.I*(s : ℂ)^2*(u : ℂ)^3/640 - Complex.I*(s : ℂ)*(u : ℂ)^3/640 - 3*(s : ℂ)*(u : ℂ)^2/320 + (u : ℂ)^2/64) * hI + (-Complex.I*(s : ℂ)^2*(u : ℂ)/640 + Complex.I*(s : ℂ)*(u : ℂ)/640 + 3*(s : ℂ)/320 - 1/64) * hu + (Complex.I*(s : ℂ)*(u : ℂ)/640 - Complex.I*(u : ℂ)/128 - (s : ℂ)/320 + 7/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-(s : ℂ)^2*(u : ℂ)/80 + (u : ℂ)/16) * hI + (Complex.I*(s : ℂ)^2/320 - Complex.I/64) * hu + (Complex.I*(s : ℂ)/160 + 3*Complex.I/160 + 3*(u : ℂ)/160) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^2*(u : ℂ)/320 - 3*Complex.I*(u : ℂ)/64 + (s : ℂ)^3/320 + (s : ℂ)^2*(u : ℂ)^2/640 - (s : ℂ)^2/320 + 3*(s : ℂ)/64 - (u : ℂ)^2/128 - 3/64) * hI + (-Complex.I*(s : ℂ)^2*(u : ℂ)/640 + Complex.I*(s : ℂ)*(u : ℂ)/640 - (s : ℂ)^2/320 + 3*(s : ℂ)/320) * hu + (-Complex.I*(s : ℂ)*(u : ℂ)/128 - 7*Complex.I*(u : ℂ)/640 - 3*(s : ℂ)/320 - 3/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^3*(u : ℂ)^2/1280 + 3*Complex.I*(s : ℂ)^2*(u : ℂ)^2/1280 - 7*Complex.I*(s : ℂ)*(u : ℂ)^2/1280 + Complex.I*(u : ℂ)^2/256 + (s : ℂ)^3*(u : ℂ)^3/2560 - (s : ℂ)^3*(u : ℂ)/640 - 3*(s : ℂ)^2*(u : ℂ)^3/2560 - 11*(s : ℂ)^2*(u : ℂ)/640 - (s : ℂ)*(u : ℂ)^3/2560 + (s : ℂ)*(u : ℂ)/128 - (u : ℂ)^3/512 - 5*(u : ℂ)/128) * hI + (3*Complex.I*(s : ℂ)^3/1280 - 11*Complex.I*(s : ℂ)^2/1280 + 21*Complex.I*(s : ℂ)/1280 - Complex.I/256 - (s : ℂ)^3*(u : ℂ)/2560 + 3*(s : ℂ)^2*(u : ℂ)/2560 + (s : ℂ)*(u : ℂ)/2560 + (u : ℂ)/512) * hu + (3*Complex.I*(s : ℂ)^2/640 + Complex.I*(s : ℂ)/320 - 21*Complex.I/640 - (s : ℂ)^2*(u : ℂ)/1280 + (s : ℂ)*(u : ℂ)/640 + 51*(u : ℂ)/1280) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (Complex.I*(s : ℂ)^2*(u : ℂ)/320 + 3*Complex.I*(u : ℂ)/64 + (s : ℂ)^3/320 + (s : ℂ)^2/320 - 5*(s : ℂ)/64 + 3/64) * hI + (-Complex.I*(s : ℂ)^3*(u : ℂ)/2560 + 3*Complex.I*(s : ℂ)^2*(u : ℂ)/2560 + Complex.I*(s : ℂ)*(u : ℂ)/2560 + Complex.I*(u : ℂ)/512 - (s : ℂ)^3/1280 + (s : ℂ)^2/256 - 7*(s : ℂ)/1280 - 1/256) * hu + (-Complex.I*(s : ℂ)^2*(u : ℂ)/1280 - Complex.I*(s : ℂ)*(u : ℂ)/640 + 7*Complex.I*(u : ℂ)/1280 - (s : ℂ)^2/640 - (s : ℂ)/320 + 11/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^3*(u : ℂ)^2/1280 + 3*Complex.I*(s : ℂ)^2*(u : ℂ)^2/1280 - 7*Complex.I*(s : ℂ)*(u : ℂ)^2/1280 + Complex.I*(u : ℂ)^2/256 + (s : ℂ)^3*(u : ℂ)/320 + (s : ℂ)^2*(u : ℂ)^3/640 - (s : ℂ)^2*(u : ℂ)/160 - (s : ℂ)*(u : ℂ)^3/640 - (s : ℂ)*(u : ℂ)/64 + (u : ℂ)/32) * hI + (Complex.I*(s : ℂ)^3/640 - 3*Complex.I*(s : ℂ)^2/640 + Complex.I*(s : ℂ)/640 + Complex.I/128 - (s : ℂ)^2*(u : ℂ)/640 + (s : ℂ)*(u : ℂ)/640) * hu + (Complex.I*(s : ℂ)^2/320 + Complex.I*(s : ℂ)/320 - Complex.I/40 - 3*(s : ℂ)*(u : ℂ)/640 + 3*(u : ℂ)/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-(s : ℂ)^2*(u : ℂ)^2/320 + 3*(s : ℂ)*(u : ℂ)^2/160 - (u : ℂ)^2/64) * hI + ((s : ℂ)^2/320 - 3*(s : ℂ)/160 + 1/64) * hu + ((s : ℂ)/160 - 3/160) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^3*(u : ℂ)^2/1280 + Complex.I*(s : ℂ)^2*(u : ℂ)^2/1280 + Complex.I*(s : ℂ)*(u : ℂ)^2/256 - Complex.I*(u : ℂ)^2/256 + (s : ℂ)^3*(u : ℂ)^3/2560 + (s : ℂ)^3*(u : ℂ)/320 - (s : ℂ)^2*(u : ℂ)^3/2560 - (s : ℂ)^2*(u : ℂ)/80 - (s : ℂ)*(u : ℂ)^3/512 - (s : ℂ)*(u : ℂ)/64 + (u : ℂ)^3/512 + (u : ℂ)/16) * hI + (Complex.I*(s : ℂ)^3/640 - Complex.I*(s : ℂ)^2/320 - Complex.I*(s : ℂ)/128 + Complex.I/64 - (s : ℂ)^3*(u : ℂ)/2560 + (s : ℂ)^2*(u : ℂ)/2560 + (s : ℂ)*(u : ℂ)/512 - (u : ℂ)/512) * hu + (Complex.I*(s : ℂ)^2/320 + Complex.I*(s : ℂ)/80 - 13*Complex.I/320 - (s : ℂ)^2*(u : ℂ)/1280 - 3*(s : ℂ)*(u : ℂ)/320 + 5*(u : ℂ)/256) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (Complex.I*(s : ℂ)^2*(u : ℂ)^3/640 - Complex.I*(s : ℂ)*(u : ℂ)^3/640 + (s : ℂ)^2*(u : ℂ)^2/320 - 3*(s : ℂ)*(u : ℂ)^2/320) * hI + (-Complex.I*(s : ℂ)^2*(u : ℂ)/640 + Complex.I*(s : ℂ)*(u : ℂ)/640 - (s : ℂ)^2/320 + 3*(s : ℂ)/320) * hu + (-Complex.I*(s : ℂ)*(u : ℂ)/128 - 7*Complex.I*(u : ℂ)/640 - 3*(s : ℂ)/320 - 3/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^3*(u : ℂ)^2/1280 + 3*Complex.I*(s : ℂ)^2*(u : ℂ)^2/1280 - 7*Complex.I*(s : ℂ)*(u : ℂ)^2/1280 + Complex.I*(u : ℂ)^2/256 + (s : ℂ)^3*(u : ℂ)/320 - (s : ℂ)^2*(u : ℂ)^3/640 - (s : ℂ)^2*(u : ℂ)/80 + (s : ℂ)*(u : ℂ)^3/640 - (s : ℂ)*(u : ℂ)/64 - (u : ℂ)/16) * hI + (Complex.I*(s : ℂ)^3/640 - Complex.I*(s : ℂ)^2/128 + 13*Complex.I*(s : ℂ)/640 - Complex.I/128 + (s : ℂ)^2*(u : ℂ)/640 - (s : ℂ)*(u : ℂ)/640) * hu + (Complex.I*(s : ℂ)^2/320 + Complex.I*(s : ℂ)/320 - Complex.I/40 + (s : ℂ)*(u : ℂ)/640 + 23*(u : ℂ)/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^3*(u : ℂ)^3/2560 + Complex.I*(s : ℂ)^2*(u : ℂ)^3/2560 + Complex.I*(s : ℂ)*(u : ℂ)^3/512 - Complex.I*(u : ℂ)^3/512 + (s : ℂ)^2*(u : ℂ)^2/640 - (u : ℂ)^2/128) * hI + (Complex.I*(s : ℂ)^3*(u : ℂ)/2560 - Complex.I*(s : ℂ)^2*(u : ℂ)/2560 - Complex.I*(s : ℂ)*(u : ℂ)/512 + Complex.I*(u : ℂ)/512 - (s : ℂ)^2/640 + 1/128) * hu + (Complex.I*(s : ℂ)^2*(u : ℂ)/1280 + Complex.I*(s : ℂ)*(u : ℂ)/320 + 7*Complex.I*(u : ℂ)/1280 - (s : ℂ)/160 - 1/160) * hs
end
end CGLMP5.Attainment
