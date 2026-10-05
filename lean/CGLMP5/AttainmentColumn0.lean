import CGLMP5.AttainmentCoefficient
namespace CGLMP5.Attainment
noncomputable section
set_option maxHeartbeats 1600000 in
/-- The five diagonal output entries for input |00>; all off-diagonal entries are separately zero. -/
lemma matrixBell_diagonal_0 (i : Fin 5) : matrixBell (i,i) (0,0) =
    toeplitzEntry i 0 := by
  have hs : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
  have hu : (u : ℂ)^2 = 10 + 2*(s : ℂ) := by exact_mod_cast u_sq
  have hI := Complex.I_sq
  simp only [matrixBell, SOS.edgeCoefficient, coefficientTable_eq, omega_pow_phase]
  fin_cases i
  · norm_num [edgeMatrix, stepMatrix_pow, Matrix.kroneckerMap_apply, Matrix.of_apply,
      stepIter, phaseIter, stepDest, stepPhase, phase, phaseTable, coefficientTable,
      toeplitzEntry, distanceIndex, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) 0 * hs
  · norm_num [edgeMatrix, stepMatrix_pow, Matrix.kroneckerMap_apply, Matrix.of_apply,
      stepIter, phaseIter, stepDest, stepPhase, phase, phaseTable, coefficientTable,
      toeplitzEntry, distanceIndex, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (Complex.I*(s : ℂ)*(u : ℂ)^2/640 + Complex.I*(u : ℂ)^2/128 - (s : ℂ)^3*(u : ℂ)^3/5120 - (s : ℂ)^3*(u : ℂ)/1280 + (s : ℂ)^2*(u : ℂ)^3/5120 - 19*(s : ℂ)^2*(u : ℂ)/1280 + 5*(s : ℂ)*(u : ℂ)^3/1024 + 29*(s : ℂ)*(u : ℂ)/1280 - 5*(u : ℂ)^3/1024 - 5*(u : ℂ)/256) * hI + (-Complex.I*(s : ℂ)^2/256 - Complex.I*(s : ℂ)/128 + 3*Complex.I/256 + (s : ℂ)^3*(u : ℂ)/5120 - (s : ℂ)^2*(u : ℂ)/5120 - 5*(s : ℂ)*(u : ℂ)/1024 + 5*(u : ℂ)/1024) * hu + (-Complex.I*(s : ℂ)/128 - Complex.I/128 + (s : ℂ)^2*(u : ℂ)/2560 + 3*(s : ℂ)*(u : ℂ)/1280 + 53*(u : ℂ)/2560) * hs
  · norm_num [edgeMatrix, stepMatrix_pow, Matrix.kroneckerMap_apply, Matrix.of_apply,
      stepIter, phaseIter, stepDest, stepPhase, phase, phaseTable, coefficientTable,
      toeplitzEntry, distanceIndex, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (3*Complex.I*(s : ℂ)^2*(u : ℂ)^3/1280 - 11*Complex.I*(s : ℂ)*(u : ℂ)^3/1280 + Complex.I*(u : ℂ)^3/128 - 3*(s : ℂ)^3*(u : ℂ)^2/1280 + 29*(s : ℂ)^2*(u : ℂ)^2/1280 - 69*(s : ℂ)*(u : ℂ)^2/1280 + 3*(u : ℂ)^2/256) * hI + (-3*Complex.I*(s : ℂ)^2*(u : ℂ)/1280 + 11*Complex.I*(s : ℂ)*(u : ℂ)/1280 - Complex.I*(u : ℂ)/128 + 3*(s : ℂ)^3/1280 - 29*(s : ℂ)^2/1280 + 69*(s : ℂ)/1280 - 3/256) * hu + (-3*Complex.I*(s : ℂ)*(u : ℂ)/256 + 9*Complex.I*(u : ℂ)/256 + 3*(s : ℂ)^2/640 - 7*(s : ℂ)/320 - 51/640) * hs
  · norm_num [edgeMatrix, stepMatrix_pow, Matrix.kroneckerMap_apply, Matrix.of_apply,
      stepIter, phaseIter, stepDest, stepPhase, phase, phaseTable, coefficientTable,
      toeplitzEntry, distanceIndex, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (3*Complex.I*(s : ℂ)^3*(u : ℂ)^2/2560 - 11*Complex.I*(s : ℂ)^2*(u : ℂ)^2/2560 + Complex.I*(s : ℂ)*(u : ℂ)^2/2560 + 3*Complex.I*(u : ℂ)^2/512 - 3*(s : ℂ)^3*(u : ℂ)/1280 - 3*(s : ℂ)^2*(u : ℂ)^3/1280 - 3*(s : ℂ)^2*(u : ℂ)/1280 + (s : ℂ)*(u : ℂ)^3/256 - 33*(s : ℂ)*(u : ℂ)/1280 + 3*(u : ℂ)/256) * hI + (-3*Complex.I*(s : ℂ)^3/1280 + Complex.I*(s : ℂ)^2/256 - Complex.I*(s : ℂ)/256 + 3*Complex.I/256 + 3*(s : ℂ)^2*(u : ℂ)/1280 - (s : ℂ)*(u : ℂ)/256) * hu + (-3*Complex.I*(s : ℂ)^2/640 - Complex.I*(s : ℂ)/64 - 5*Complex.I/128 + 9*(s : ℂ)*(u : ℂ)/1280 + 13*(u : ℂ)/1280) * hs
  · norm_num [edgeMatrix, stepMatrix_pow, Matrix.kroneckerMap_apply, Matrix.of_apply,
      stepIter, phaseIter, stepDest, stepPhase, phase, phaseTable, coefficientTable,
      toeplitzEntry, distanceIndex, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) (-Complex.I*(s : ℂ)^3*(u : ℂ)^3/5120 - 7*Complex.I*(s : ℂ)^2*(u : ℂ)^3/5120 - 7*Complex.I*(s : ℂ)*(u : ℂ)^3/5120 + 3*Complex.I*(u : ℂ)^3/1024 - (s : ℂ)^3*(u : ℂ)^2/640 - (s : ℂ)^2*(u : ℂ)^2/256 - 9*(s : ℂ)*(u : ℂ)^2/320 - (u : ℂ)^2/256) * hI + (Complex.I*(s : ℂ)^3*(u : ℂ)/5120 + 7*Complex.I*(s : ℂ)^2*(u : ℂ)/5120 + 7*Complex.I*(s : ℂ)*(u : ℂ)/5120 - 3*Complex.I*(u : ℂ)/1024 + (s : ℂ)^3/640 + (s : ℂ)^2/256 + 9*(s : ℂ)/320 + 1/256) * hu + (Complex.I*(s : ℂ)^2*(u : ℂ)/2560 + 3*Complex.I*(s : ℂ)*(u : ℂ)/1280 + Complex.I*(u : ℂ)/512 + (s : ℂ)^2/320 + 3*(s : ℂ)/128 + 61/640) * hs
end
end CGLMP5.Attainment
