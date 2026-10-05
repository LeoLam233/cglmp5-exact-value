import CGLMP5.SOSFeatureData
import CGLMP5.ScalarConstantsData
import CGLMP5.SOSDefinitions
import CGLMP5.AttainmentPhases
import Mathlib.Tactic.Abel

/-! The reflected target is the literal finite-Fourier Bell polynomial. -/

namespace CGLMP5.SOSFinite

set_option Elab.async false

/-- The four groups of four nonconstant target coefficients, in source order. -/
def targetEdge (r k : Fin 4) : Scalar :=
  ((targetPolynomial[1+4*r.val+k.val]?).getD (Word.one, Scalar.zero)).2

set_option maxRecDepth 20000 in
lemma target_layout : targetPolynomial =
    (Word.one, Scalar.muExact) :: (List.finRange 4).flatMap fun r =>
      (List.finRange 4).map fun k => (SOS.edgeWord r (k.val+1), targetEdge r k) := by
  decide +kernel

lemma omega_pow_phase (n : ℕ) : (zeta^4)^n = Attainment.phase (4*n) := by
  rw [Attainment.phase_eq_pow, pow_mul]

set_option maxHeartbeats 2000000 in
lemma targetEdge_eval (r k : Fin 4) :
    Scalar.eval (targetEdge r k) = -SOS.edgeCoefficient (zeta^4) r (k.val+1) := by
  simp only [SOS.edgeCoefficient, SOS.fourierCoeff]
  simp_rw [omega_pow_phase]
  fin_cases r <;> fin_cases k <;>
    norm_num [targetEdge, targetPolynomial, Scalar.eval, Scalar.ofCanonical,
      Scalar.basisEval, Fin.sum_univ_succ, Attainment.phase, Attainment.phaseTable]
  all_goals ring_nf
  all_goals try simp only [Scalar.sC_sq, Scalar.uC_sq, Complex.I_sq]
  all_goals ring_nf
  all_goals try simp only [Scalar.sC_sq, Scalar.uC_sq, Complex.I_sq]
  all_goals ring

end CGLMP5.SOSFinite
