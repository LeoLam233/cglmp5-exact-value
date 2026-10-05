import CGLMP5.AttainmentMatrixDefs
namespace CGLMP5.Attainment
noncomputable section
set_option maxHeartbeats 1200000 in
/-- Exact25-entry Fourier/spectral bridge for measurement r=3. -/
lemma localSpectral_step_3 : localSpectral 3 = stepMatrix 3 := by
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
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-(s : ℂ)^2*(u : ℂ)/160 + (s : ℂ)*(u : ℂ)/16 - (u : ℂ)/32) * hI + (Complex.I*(s : ℂ)/80) * hu + (Complex.I/80) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) ((s : ℂ)^2*(u : ℂ)^2/320 - (u : ℂ)^2/64) * hI + (1/64 - (s : ℂ)^2/320) * hu + (Complex.I*(u : ℂ)/160 - (s : ℂ)/160 - 7/160) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-(s : ℂ)^2*(u : ℂ)/160 + (u : ℂ)/32) * hI + (Complex.I*(s : ℂ)^2/320 - Complex.I/64) * hu + (Complex.I*(s : ℂ)/160 + 3*Complex.I/160 + 3*(u : ℂ)/160) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) ((s : ℂ)*(u : ℂ)^2/80) * hI + (-(s : ℂ)/80) * hu + (-Complex.I*(u : ℂ)/80 - 3/80) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) ((s : ℂ)^2*(u : ℂ)/160 - (s : ℂ)*(u : ℂ)/16 + (u : ℂ)/32) * hI + (Complex.I*(s : ℂ)/80) * hu + (3*Complex.I/80 - (u : ℂ)/80) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (Complex.I*(s : ℂ)^3*(u : ℂ)/640 - 3*Complex.I*(s : ℂ)^2*(u : ℂ)/640 - Complex.I*(s : ℂ)*(u : ℂ)/128 + 3*Complex.I*(u : ℂ)/128 - (s : ℂ)^3/320 - 3*(s : ℂ)^2/320 + (s : ℂ)/64 + 3/64) * hI + (-Complex.I*(s : ℂ)^2*(u : ℂ)/1280 + Complex.I*(u : ℂ)/256 + (s : ℂ)^3/1280 + (s : ℂ)^2/1280 - (s : ℂ)/256 - 1/256) * hu + (-Complex.I*(s : ℂ)*(u : ℂ)/320 - Complex.I*(u : ℂ)/320 + (s : ℂ)^2/640 + (s : ℂ)/80 + 11/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^3*(u : ℂ)^2/1280 + Complex.I*(s : ℂ)^2*(u : ℂ)^2/1280 - 3*Complex.I*(s : ℂ)*(u : ℂ)^2/1280 - Complex.I*(u : ℂ)^2/256 - (s : ℂ)^3*(u : ℂ)/640 - (s : ℂ)^2*(u : ℂ)^3/1280 + (s : ℂ)^2*(u : ℂ)/128 + 3*(s : ℂ)*(u : ℂ)^3/640 + (s : ℂ)*(u : ℂ)/128 - (u : ℂ)^3/256 - 5*(u : ℂ)/128) * hI + (Complex.I*(s : ℂ)^3/1280 - 3*Complex.I*(s : ℂ)^2/1280 + 3*Complex.I*(s : ℂ)/1280 + 3*Complex.I/256 + (s : ℂ)^2*(u : ℂ)/1280 - 3*(s : ℂ)*(u : ℂ)/640 + (u : ℂ)/256) * hu + (Complex.I*(s : ℂ)^2/640 - 9*Complex.I/640 + 3*(s : ℂ)*(u : ℂ)/640 - 9*(u : ℂ)/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (Complex.I*(s : ℂ)^3*(u : ℂ)/640 - Complex.I*(s : ℂ)^2*(u : ℂ)/640 + 3*Complex.I*(s : ℂ)*(u : ℂ)/128 - 3*Complex.I*(u : ℂ)/128 - (s : ℂ)^3*(u : ℂ)^2/1280 - (s : ℂ)^3/320 + (s : ℂ)^2*(u : ℂ)^2/1280 - (s : ℂ)^2/320 + (s : ℂ)*(u : ℂ)^2/256 - 3*(s : ℂ)/64 - (u : ℂ)^2/256 - 3/64) * hI + (-Complex.I*(s : ℂ)^2*(u : ℂ)/1280 + 3*Complex.I*(s : ℂ)*(u : ℂ)/640 - Complex.I*(u : ℂ)/256 + (s : ℂ)^3/1280 - 3*(s : ℂ)^2/1280 - 13*(s : ℂ)/1280 + 3/256) * hu + (-3*Complex.I*(s : ℂ)*(u : ℂ)/640 + Complex.I*(u : ℂ)/128 + (s : ℂ)^2/640 + (s : ℂ)/160 - 21/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-(s : ℂ)^2*(u : ℂ)^3/1280 - (s : ℂ)^2*(u : ℂ)/320 + (u : ℂ)^3/256 + (u : ℂ)/64) * hI + (Complex.I*(s : ℂ)^3/1280 + Complex.I*(s : ℂ)^2/1280 - Complex.I*(s : ℂ)/256 - Complex.I/256 + (s : ℂ)^2*(u : ℂ)/1280 - (u : ℂ)/256) * hu + (Complex.I*(s : ℂ)^2/640 + Complex.I*(s : ℂ)/160 - Complex.I/640 + (s : ℂ)*(u : ℂ)/320 + 3*(u : ℂ)/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-(s : ℂ)^2*(u : ℂ)^2/320 + (u : ℂ)^2/64) * hI + ((s : ℂ)^2/320 - 1/64) * hu + (-3*Complex.I*(u : ℂ)/160 + (s : ℂ)/160 + 3/160) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^3*(u : ℂ)^2/1280 + Complex.I*(s : ℂ)^2*(u : ℂ)^2/1280 - 3*Complex.I*(s : ℂ)*(u : ℂ)^2/1280 - Complex.I*(u : ℂ)^2/256 - 3*(s : ℂ)^3*(u : ℂ)/640 + (s : ℂ)^2*(u : ℂ)^3/1280 + 7*(s : ℂ)^2*(u : ℂ)/640 - 3*(s : ℂ)*(u : ℂ)^3/640 - 5*(s : ℂ)*(u : ℂ)/128 + (u : ℂ)^3/256 + (u : ℂ)/128) * hI + (Complex.I*(s : ℂ)^3/1280 + Complex.I*(s : ℂ)^2/1280 + 19*Complex.I*(s : ℂ)/1280 - Complex.I/256 - (s : ℂ)^2*(u : ℂ)/1280 + 3*(s : ℂ)*(u : ℂ)/640 - (u : ℂ)/256) * hu + (Complex.I*(s : ℂ)^2/640 + Complex.I*(s : ℂ)/80 + 31*Complex.I/640 + 3*(s : ℂ)*(u : ℂ)/640 - 9*(u : ℂ)/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (Complex.I*(s : ℂ)^3*(u : ℂ)^3/2560 - Complex.I*(s : ℂ)^2*(u : ℂ)^3/512 + 7*Complex.I*(s : ℂ)*(u : ℂ)^3/2560 + Complex.I*(u : ℂ)^3/512 + (s : ℂ)^2*(u : ℂ)^2/640 - (s : ℂ)*(u : ℂ)^2/160 - (u : ℂ)^2/128) * hI + (-Complex.I*(s : ℂ)^3*(u : ℂ)/2560 + Complex.I*(s : ℂ)^2*(u : ℂ)/512 - 7*Complex.I*(s : ℂ)*(u : ℂ)/2560 - Complex.I*(u : ℂ)/512 - (s : ℂ)^2/640 + (s : ℂ)/160 + 1/128) * hu + (-Complex.I*(s : ℂ)^2*(u : ℂ)/1280 - Complex.I*(s : ℂ)*(u : ℂ)/640 + 11*Complex.I*(u : ℂ)/1280 - 1/160) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^3*(u : ℂ)^2/1280 - Complex.I*(s : ℂ)^2*(u : ℂ)^2/1280 - 3*Complex.I*(s : ℂ)*(u : ℂ)^2/1280 + Complex.I*(u : ℂ)^2/256 + (s : ℂ)^3*(u : ℂ)^3/2560 - 3*(s : ℂ)^3*(u : ℂ)/640 - (s : ℂ)^2*(u : ℂ)^3/512 + (s : ℂ)^2*(u : ℂ)/640 + 7*(s : ℂ)*(u : ℂ)^3/2560 + 3*(s : ℂ)*(u : ℂ)/128 + (u : ℂ)^3/512 - (u : ℂ)/128) * hI + (Complex.I*(s : ℂ)^3/640 + Complex.I*(s : ℂ)^2/320 - Complex.I*(s : ℂ)/640 - Complex.I/64 - (s : ℂ)^3*(u : ℂ)/2560 + (s : ℂ)^2*(u : ℂ)/512 - 7*(s : ℂ)*(u : ℂ)/2560 - (u : ℂ)/512) * hu + (Complex.I*(s : ℂ)^2/320 + Complex.I*(s : ℂ)/40 + 13*Complex.I/320 - (s : ℂ)^2*(u : ℂ)/1280 + (s : ℂ)*(u : ℂ)/128 + 7*(u : ℂ)/1280) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (Complex.I*(s : ℂ)^2*(u : ℂ)^3/1280 - 3*Complex.I*(s : ℂ)*(u : ℂ)^3/640 + Complex.I*(u : ℂ)^3/256 - (s : ℂ)^3*(u : ℂ)^2/1280 + 3*(s : ℂ)^2*(u : ℂ)^2/1280 + 13*(s : ℂ)*(u : ℂ)^2/1280 - 3*(u : ℂ)^2/256) * hI + (-Complex.I*(s : ℂ)^2*(u : ℂ)/1280 + 3*Complex.I*(s : ℂ)*(u : ℂ)/640 - Complex.I*(u : ℂ)/256 + (s : ℂ)^3/1280 - 3*(s : ℂ)^2/1280 - 13*(s : ℂ)/1280 + 3/256) * hu + (-3*Complex.I*(s : ℂ)*(u : ℂ)/640 + Complex.I*(u : ℂ)/128 + (s : ℂ)^2/640 + (s : ℂ)/160 - 21/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) ((s : ℂ)^2*(u : ℂ)/160 - (u : ℂ)/32) * hI + (Complex.I*(s : ℂ)^2/320 - Complex.I/64) * hu + (Complex.I*(s : ℂ)/160 + 7*Complex.I/160 + (u : ℂ)/160) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (Complex.I*(s : ℂ)^3*(u : ℂ)/640 - Complex.I*(s : ℂ)^2*(u : ℂ)/640 + 3*Complex.I*(s : ℂ)*(u : ℂ)/128 - 3*Complex.I*(u : ℂ)/128 + (s : ℂ)^3*(u : ℂ)^2/1280 - (s : ℂ)^3/320 - (s : ℂ)^2*(u : ℂ)^2/1280 - (s : ℂ)^2/320 - (s : ℂ)*(u : ℂ)^2/256 - 3*(s : ℂ)/64 + (u : ℂ)^2/256 - 3/64) * hI + (-Complex.I*(s : ℂ)^2*(u : ℂ)/1280 + 3*Complex.I*(s : ℂ)*(u : ℂ)/640 - Complex.I*(u : ℂ)/256 - (s : ℂ)^3/1280 - (s : ℂ)^2/1280 - 3*(s : ℂ)/1280 + 1/256) * hu + (-Complex.I*(s : ℂ)*(u : ℂ)/640 - Complex.I*(u : ℂ)/640 - (s : ℂ)^2/640 - (s : ℂ)/160 - 11/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^3*(u : ℂ)^2/1280 - Complex.I*(s : ℂ)^2*(u : ℂ)^2/1280 - 3*Complex.I*(s : ℂ)*(u : ℂ)^2/1280 + Complex.I*(u : ℂ)^2/256 - (s : ℂ)^3*(u : ℂ)^3/2560 - (s : ℂ)^3*(u : ℂ)/640 + (s : ℂ)^2*(u : ℂ)^3/512 + 3*(s : ℂ)^2*(u : ℂ)/640 - 7*(s : ℂ)*(u : ℂ)^3/2560 - 7*(s : ℂ)*(u : ℂ)/128 - (u : ℂ)^3/512 + 5*(u : ℂ)/128) * hI + (Complex.I*(s : ℂ)^3/640 + 7*Complex.I*(s : ℂ)/640 + (s : ℂ)^3*(u : ℂ)/2560 - (s : ℂ)^2*(u : ℂ)/512 + 7*(s : ℂ)*(u : ℂ)/2560 + (u : ℂ)/512) * hu + (Complex.I*(s : ℂ)^2/320 + Complex.I*(s : ℂ)/80 + 13*Complex.I/320 + (s : ℂ)^2*(u : ℂ)/1280 + 3*(s : ℂ)*(u : ℂ)/640 - 23*(u : ℂ)/1280) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (Complex.I*(s : ℂ)^3*(u : ℂ)/640 + Complex.I*(s : ℂ)^2*(u : ℂ)/640 - 5*Complex.I*(s : ℂ)*(u : ℂ)/128 + 3*Complex.I*(u : ℂ)/128 - (s : ℂ)^3/320 + (s : ℂ)^2/320 + 5*(s : ℂ)/64 + 3/64) * hI + (-Complex.I*(s : ℂ)^3*(u : ℂ)/2560 + Complex.I*(s : ℂ)^2*(u : ℂ)/512 - 7*Complex.I*(s : ℂ)*(u : ℂ)/2560 - Complex.I*(u : ℂ)/512 - (s : ℂ)^2/640 + (s : ℂ)/160 + 1/128) * hu + (-Complex.I*(s : ℂ)^2*(u : ℂ)/1280 - Complex.I*(s : ℂ)*(u : ℂ)/640 + 11*Complex.I*(u : ℂ)/1280 - 1/160) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)*(u : ℂ)^2/160 - (s : ℂ)^2*(u : ℂ)^3/1280 + (s : ℂ)^2*(u : ℂ)/320 + 3*(s : ℂ)*(u : ℂ)^3/640 - (u : ℂ)^3/256 - (u : ℂ)/64) * hI + (Complex.I*(s : ℂ)^3/1280 - 3*Complex.I*(s : ℂ)^2/1280 + 3*Complex.I*(s : ℂ)/1280 + 3*Complex.I/256 + (s : ℂ)^2*(u : ℂ)/1280 - 3*(s : ℂ)*(u : ℂ)/640 + (u : ℂ)/256) * hu + (Complex.I*(s : ℂ)^2/640 - 9*Complex.I/640 + 3*(s : ℂ)*(u : ℂ)/640 - 9*(u : ℂ)/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-(s : ℂ)*(u : ℂ)^2/80) * hI + ((s : ℂ)/80) * hu + (1/80) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-(s : ℂ)^3*(u : ℂ)/320 + (s : ℂ)^2*(u : ℂ)^3/1280 + (s : ℂ)^2*(u : ℂ)/160 + (s : ℂ)*(u : ℂ)/64 - (u : ℂ)^3/256 - (u : ℂ)/32) * hI + (-Complex.I*(s : ℂ)^3/1280 - Complex.I*(s : ℂ)^2/1280 + Complex.I*(s : ℂ)/256 + Complex.I/256 - (s : ℂ)^2*(u : ℂ)/1280 + (u : ℂ)/256) * hu + (-Complex.I*(s : ℂ)^2/640 - Complex.I*(s : ℂ)/160 + Complex.I/640 + (s : ℂ)*(u : ℂ)/320 - (u : ℂ)/64) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (Complex.I*(s : ℂ)^2*(u : ℂ)^3/1280 - 3*Complex.I*(s : ℂ)*(u : ℂ)^3/640 + Complex.I*(u : ℂ)^3/256 + (s : ℂ)^3*(u : ℂ)^2/1280 + (s : ℂ)^2*(u : ℂ)^2/1280 + 3*(s : ℂ)*(u : ℂ)^2/1280 - (u : ℂ)^2/256) * hI + (-Complex.I*(s : ℂ)^2*(u : ℂ)/1280 + 3*Complex.I*(s : ℂ)*(u : ℂ)/640 - Complex.I*(u : ℂ)/256 - (s : ℂ)^3/1280 - (s : ℂ)^2/1280 - 3*(s : ℂ)/1280 + 1/256) * hu + (-Complex.I*(s : ℂ)*(u : ℂ)/640 - Complex.I*(u : ℂ)/640 - (s : ℂ)^2/640 - (s : ℂ)/160 - 11/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)*(u : ℂ)^2/160 - (s : ℂ)^3*(u : ℂ)/320 + (s : ℂ)^2*(u : ℂ)^3/1280 + (s : ℂ)^2*(u : ℂ)/160 - 3*(s : ℂ)*(u : ℂ)^3/640 - 3*(s : ℂ)*(u : ℂ)/64 + (u : ℂ)^3/256 + (u : ℂ)/32) * hI + (Complex.I*(s : ℂ)^3/1280 + Complex.I*(s : ℂ)^2/1280 + 19*Complex.I*(s : ℂ)/1280 - Complex.I/256 - (s : ℂ)^2*(u : ℂ)/1280 + 3*(s : ℂ)*(u : ℂ)/640 - (u : ℂ)/256) * hu + (Complex.I*(s : ℂ)^2/640 + Complex.I*(s : ℂ)/80 + 31*Complex.I/640 + 3*(s : ℂ)*(u : ℂ)/640 - 9*(u : ℂ)/640) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (Complex.I*(s : ℂ)^2*(u : ℂ)^3/1280 - Complex.I*(u : ℂ)^3/256 - (s : ℂ)^3*(u : ℂ)^2/1280 - (s : ℂ)^2*(u : ℂ)^2/1280 + (s : ℂ)*(u : ℂ)^2/256 + (u : ℂ)^2/256) * hI + (-Complex.I*(s : ℂ)^2*(u : ℂ)/1280 + Complex.I*(u : ℂ)/256 + (s : ℂ)^3/1280 + (s : ℂ)^2/1280 - (s : ℂ)/256 - 1/256) * hu + (-Complex.I*(s : ℂ)*(u : ℂ)/320 - Complex.I*(u : ℂ)/320 + (s : ℂ)^2/640 + (s : ℂ)/80 + 11/640) * hs
end
end CGLMP5.Attainment
