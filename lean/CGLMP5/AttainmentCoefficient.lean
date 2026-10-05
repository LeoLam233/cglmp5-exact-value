import CGLMP5.AttainmentBellDefs
namespace CGLMP5.Attainment
noncomputable section

def coefficientTable : Fin 4 → ℂ :=
  ![-Complex.I*(s : ℂ)*(u : ℂ)/80 - Complex.I*(u : ℂ)/16 + 1/4,
    -3*Complex.I*(s : ℂ)*(u : ℂ)/80 + Complex.I*(u : ℂ)/16 + 1/4,
    3*Complex.I*(s : ℂ)*(u : ℂ)/80 - Complex.I*(u : ℂ)/16 + 1/4,
    Complex.I*(s : ℂ)*(u : ℂ)/80 + Complex.I*(u : ℂ)/16 + 1/4]

lemma omega_pow_phase (k : ℕ) : (zeta^4)^k = phase (4*k) := by
  rw [← pow_mul, phase_eq_pow]

lemma coefficientTable_eq (k : Fin 4) : SOS.fourierCoeff (zeta^4) (k.val+1) = coefficientTable k := by
  have hs : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
  have hu : (u : ℂ)^2 = 10 + 2*(s : ℂ) := by exact_mod_cast u_sq
  have hI := Complex.I_sq
  simp only [SOS.fourierCoeff, omega_pow_phase]
  fin_cases k
  · norm_num [phase, phaseTable, coefficientTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) 0 * hs
  · norm_num [phase, phaseTable, coefficientTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) 0 * hs
  · norm_num [phase, phaseTable, coefficientTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) 0 * hs
  · norm_num [phase, phaseTable, coefficientTable, Fin.sum_univ_succ]
    all_goals linear_combination (norm := (ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring)) 0 * hs
end
end CGLMP5.Attainment
