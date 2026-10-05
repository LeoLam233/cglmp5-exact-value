import CGLMP5.AttainmentPhases

namespace CGLMP5.Attainment
noncomputable section
open scoped BigOperators

/-- r=0,2 are Alice settings0,1; r=1,3 are Bob settings0,1.
The exponents are exactly j*(4a+2x) and j*(-4b+1-2y), modulo20. -/
def phaseExponent (r : Fin 4) (a j : Fin 5) : ℕ :=
  (![4*a.val, 21-4*a.val, 4*a.val+2, 19-4*a.val] r) * j.val

set_option maxHeartbeats 2000000 in
/-- Exact cancellation of fifth roots of unity, for all four actual offset choices. -/
lemma phase_overlap (r : Fin 4) (a b : Fin 5) :
    (∑ j : Fin 5, star (phase (phaseExponent r a j)) * phase (phaseExponent r b j)) =
      if a = b then (5 : ℂ) else 0 := by
  have hs : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
  have hu : (u : ℂ)^2 = 10 + 2*(s : ℂ) := by exact_mod_cast u_sq
  have hI := Complex.I_sq
  simp only [star_phase]
  fin_cases r <;> fin_cases a <;> fin_cases b
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/32 + (s : ℂ)*(u : ℂ)^2/16 - 5*(u : ℂ)^2/32) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/32 - (s : ℂ)*(u : ℂ)^2/16 + 5*(u : ℂ)^2/32) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/32 + (s : ℂ)*(u : ℂ)^2/16 - 5*(u : ℂ)^2/32) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/32 - (s : ℂ)*(u : ℂ)^2/16 + 5*(u : ℂ)^2/32) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/32 - (s : ℂ)*(u : ℂ)^2/16 + 5*(u : ℂ)^2/32) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/32 + (s : ℂ)*(u : ℂ)^2/16 - 5*(u : ℂ)^2/32) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/32 - (s : ℂ)*(u : ℂ)^2/16 + 5*(u : ℂ)^2/32) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/32 + (s : ℂ)*(u : ℂ)^2/16 - 5*(u : ℂ)^2/32) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 + (s : ℂ)*(u : ℂ)^2/32 - 5*(u : ℂ)^2/64 - 1/8) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 - (s : ℂ)*(u : ℂ)^2/32 + 5*(u : ℂ)^2/64 - 1/8) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 + (s : ℂ)*(u : ℂ)^2/32 - 5*(u : ℂ)^2/64 - 1/8) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 - (s : ℂ)*(u : ℂ)^2/32 + 5*(u : ℂ)^2/64 - 1/8) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 - (s : ℂ)*(u : ℂ)^2/32 + 5*(u : ℂ)^2/64 - 1/8) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 + (s : ℂ)*(u : ℂ)^2/32 - 5*(u : ℂ)^2/64 - 1/8) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 - (s : ℂ)*(u : ℂ)^2/32 + 5*(u : ℂ)^2/64 - 1/8) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 + (s : ℂ)*(u : ℂ)^2/32 - 5*(u : ℂ)^2/64 - 1/8) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/32 + (s : ℂ)*(u : ℂ)^2/16 - 5*(u : ℂ)^2/32) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/32 - (s : ℂ)*(u : ℂ)^2/16 + 5*(u : ℂ)^2/32) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/32 + (s : ℂ)*(u : ℂ)^2/16 - 5*(u : ℂ)^2/32) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/32 - (s : ℂ)*(u : ℂ)^2/16 + 5*(u : ℂ)^2/32) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/32 - (s : ℂ)*(u : ℂ)^2/16 + 5*(u : ℂ)^2/32) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/32 + (s : ℂ)*(u : ℂ)^2/16 - 5*(u : ℂ)^2/32) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/32 - (s : ℂ)*(u : ℂ)^2/16 + 5*(u : ℂ)^2/32) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination 0 * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/32 + (s : ℂ)*(u : ℂ)^2/16 - 5*(u : ℂ)^2/32) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 + (s : ℂ)*(u : ℂ)^2/32 - 5*(u : ℂ)^2/64 - 1/8) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 - (s : ℂ)*(u : ℂ)^2/32 + 5*(u : ℂ)^2/64 - 1/8) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 - (s : ℂ)*(u : ℂ)^2/32 + 5*(u : ℂ)^2/64 - 1/8) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 + (s : ℂ)*(u : ℂ)^2/32 - 5*(u : ℂ)^2/64 - 1/8) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 + (s : ℂ)*(u : ℂ)^2/32 - 5*(u : ℂ)^2/64 - 1/8) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 - (s : ℂ)*(u : ℂ)^2/32 + 5*(u : ℂ)^2/64 - 1/8) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (1/2) * hI
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2/8 - 1/8) * hI + (-1/4) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination ((s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 - (s : ℂ)*(u : ℂ)^2/32 + 5*(u : ℂ)^2/64 - 1/8) * hI + (-(s : ℂ)^2/32 + (s : ℂ)/16 - 5/32) * hu + (1/16 - (s : ℂ)/16) * hs
  · norm_num [phaseExponent, phase, phaseTable, Fin.sum_univ_succ]
    all_goals linear_combination (-(s : ℂ)^2*(u : ℂ)^2/64 - (s : ℂ)^2/8 + (s : ℂ)*(u : ℂ)^2/32 - 5*(u : ℂ)^2/64 - 1/8) * hI + ((s : ℂ)^2/32 - (s : ℂ)/16 + 5/32) * hu + ((s : ℂ)/16 + 7/16) * hs

end
end CGLMP5.Attainment
