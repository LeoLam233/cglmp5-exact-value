import CGLMP5.AttainmentMatrixDefs
namespace CGLMP5.Attainment
noncomputable section
set_option maxHeartbeats 1200000 in
/-- Exact25-entry Fourier/spectral bridge for measurement r=0. -/
lemma localSpectral_step_0 : localSpectral 0 = stepMatrix 0 := by
  have hs : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
  have hu : (u : ℂ)^2 = 10 + 2*(s : ℂ) := by exact_mod_cast u_sq
  have hI := Complex.I_sq
  ext i j
  fin_cases i <;> fin_cases j
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/160 + (s : ℂ)*(u : ℂ)^2/80 - (u : ℂ)^2/32) * hI + ((s : ℂ)^2/160 - (s : ℂ)/80 + 1/32) * hu + ((s : ℂ)/80 + 7/80) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/20) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/20) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/160 - (s : ℂ)*(u : ℂ)^2/80 + (u : ℂ)^2/32) * hI + (-(s : ℂ)^2/160 + (s : ℂ)/80 - 1/32) * hu + (1/80 - (s : ℂ)/80) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/160 - (s : ℂ)*(u : ℂ)^2/80 + (u : ℂ)^2/32) * hI + (-(s : ℂ)^2/160 + (s : ℂ)/80 - 1/32) * hu + (1/80 - (s : ℂ)/80) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^3*(u : ℂ)^2/640 - (s : ℂ)^2*(u : ℂ)^2/640 - (s : ℂ)*(u : ℂ)^2/128 + (u : ℂ)^2/128) * hI + (-(s : ℂ)^3/640 + (s : ℂ)^2/640 + (s : ℂ)/128 - 1/128) * hu + (-(s : ℂ)^2/320 - (s : ℂ)/80 - 7/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^3*(u : ℂ)^2/640 - 11*(s : ℂ)^2*(u : ℂ)^2/640 + 7*(s : ℂ)*(u : ℂ)^2/640 - (u : ℂ)^2/128) * hI + (-(s : ℂ)^3/640 + 11*(s : ℂ)^2/640 - 7*(s : ℂ)/640 + 1/128) * hu + (-(s : ℂ)^2/320 + 3*(s : ℂ)/160 + 47/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^3*(u : ℂ)^2/640 + (s : ℂ)^2*(u : ℂ)^2/128 - 9*(s : ℂ)*(u : ℂ)^2/640 - (u : ℂ)^2/128) * hI + (-(s : ℂ)^3/640 - (s : ℂ)^2/128 + 9*(s : ℂ)/640 + 1/128) * hu + (-(s : ℂ)^2/320 - (s : ℂ)/32 - 17/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-3*(s : ℂ)^3*(u : ℂ)^2/640 + 3*(s : ℂ)^2*(u : ℂ)^2/640 + 3*(s : ℂ)*(u : ℂ)^2/128 - 3*(u : ℂ)^2/128) * hI + (3*(s : ℂ)^3/640 - 3*(s : ℂ)^2/640 - 3*(s : ℂ)/128 + 3/128) * hu + (3*(s : ℂ)^2/320 + 3*(s : ℂ)/80 - 27/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/20) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^3*(u : ℂ)^2/640 + 3*(s : ℂ)^2*(u : ℂ)^2/640 + (s : ℂ)*(u : ℂ)^2/640 + (u : ℂ)^2/128) * hI + ((s : ℂ)^3/640 - 3*(s : ℂ)^2/640 - (s : ℂ)/640 - 1/128) * hu + ((s : ℂ)^2/320 + (s : ℂ)/160 - 7/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^3*(u : ℂ)^2/640 + 3*(s : ℂ)^2*(u : ℂ)^2/640 + (s : ℂ)*(u : ℂ)^2/640 + (u : ℂ)^2/128) * hI + ((s : ℂ)^3/640 - 3*(s : ℂ)^2/640 - (s : ℂ)/640 - 1/128) * hu + ((s : ℂ)^2/320 + (s : ℂ)/160 - 7/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^3*(u : ℂ)^2/640 - 11*(s : ℂ)^2*(u : ℂ)^2/640 + 7*(s : ℂ)*(u : ℂ)^2/640 - (u : ℂ)^2/128) * hI + (-(s : ℂ)^3/640 + 11*(s : ℂ)^2/640 - 7*(s : ℂ)/640 + 1/128) * hu + (-(s : ℂ)^2/320 + 3*(s : ℂ)/160 + 47/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^3*(u : ℂ)^2/640 + (s : ℂ)^2*(u : ℂ)^2/128 - 9*(s : ℂ)*(u : ℂ)^2/640 - (u : ℂ)^2/128) * hI + (-(s : ℂ)^3/640 - (s : ℂ)^2/128 + 9*(s : ℂ)/640 + 1/128) * hu + (-(s : ℂ)^2/320 - (s : ℂ)/32 - 17/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/20) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^3*(u : ℂ)^2/640 + 3*(s : ℂ)^2*(u : ℂ)^2/640 + (s : ℂ)*(u : ℂ)^2/640 + (u : ℂ)^2/128) * hI + ((s : ℂ)^3/640 - 3*(s : ℂ)^2/640 - (s : ℂ)/640 - 1/128) * hu + ((s : ℂ)^2/320 + (s : ℂ)/160 - 7/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^3*(u : ℂ)^2/640 + (s : ℂ)^2*(u : ℂ)^2/128 - 9*(s : ℂ)*(u : ℂ)^2/640 - (u : ℂ)^2/128) * hI + (-(s : ℂ)^3/640 - (s : ℂ)^2/128 + 9*(s : ℂ)/640 + 1/128) * hu + (-(s : ℂ)^2/320 - (s : ℂ)/32 - 17/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^3*(u : ℂ)^2/640 + 3*(s : ℂ)^2*(u : ℂ)^2/640 + (s : ℂ)*(u : ℂ)^2/640 + (u : ℂ)^2/128) * hI + ((s : ℂ)^3/640 - 3*(s : ℂ)^2/640 - (s : ℂ)/640 - 1/128) * hu + ((s : ℂ)^2/320 + (s : ℂ)/160 - 7/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^3*(u : ℂ)^2/640 - 11*(s : ℂ)^2*(u : ℂ)^2/640 + 7*(s : ℂ)*(u : ℂ)^2/640 - (u : ℂ)^2/128) * hI + (-(s : ℂ)^3/640 + 11*(s : ℂ)^2/640 - 7*(s : ℂ)/640 + 1/128) * hu + (-(s : ℂ)^2/320 + 3*(s : ℂ)/160 + 47/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/160 + (s : ℂ)*(u : ℂ)^2/80 - (u : ℂ)^2/32) * hI + ((s : ℂ)^2/160 - (s : ℂ)/80 + 1/32) * hu + ((s : ℂ)/80 + 7/80) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^3*(u : ℂ)^2/640 - (s : ℂ)^2*(u : ℂ)^2/640 - (s : ℂ)*(u : ℂ)^2/128 + (u : ℂ)^2/128) * hI + (-(s : ℂ)^3/640 + (s : ℂ)^2/640 + (s : ℂ)/128 - 1/128) * hu + (-(s : ℂ)^2/320 - (s : ℂ)/80 - 7/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^3*(u : ℂ)^2/640 + 3*(s : ℂ)^2*(u : ℂ)^2/640 + (s : ℂ)*(u : ℂ)^2/640 + (u : ℂ)^2/128) * hI + ((s : ℂ)^3/640 - 3*(s : ℂ)^2/640 - (s : ℂ)/640 - 1/128) * hu + ((s : ℂ)^2/320 + (s : ℂ)/160 - 7/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^3*(u : ℂ)^2/640 + 3*(s : ℂ)^2*(u : ℂ)^2/640 + (s : ℂ)*(u : ℂ)^2/640 + (u : ℂ)^2/128) * hI + ((s : ℂ)^3/640 - 3*(s : ℂ)^2/640 - (s : ℂ)/640 - 1/128) * hu + ((s : ℂ)^2/320 + (s : ℂ)/160 - 7/320) * hs
  · norm_num [localSpectral, localMatrix, stepMatrix, stepDest, stepPhase,
      matrixPhaseExponent, star_phase, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^3*(u : ℂ)^2/640 - (s : ℂ)^2*(u : ℂ)^2/640 - (s : ℂ)*(u : ℂ)^2/128 + (u : ℂ)^2/128) * hI + (-(s : ℂ)^3/640 + (s : ℂ)^2/640 + (s : ℂ)/128 - 1/128) * hu + (-(s : ℂ)^2/320 - (s : ℂ)/80 - 7/320) * hs
end
end CGLMP5.Attainment
