import CGLMP5.SOSCompressedChecks
import CGLMP5.SOSPhaseChecks
import CGLMP5.SOSExpansionChecks
import CGLMP5.SOSPhaseLink
import CGLMP5.SOSSemanticsCore
import CGLMP5.Scalar

/-! Actual scalar and representation semantics of the phase-compressed finite expansion. -/
namespace CGLMP5.SOSFinite
noncomputable section

theorem gram_evaluation (h : Fin 135) :
    Scalar.eval (gram h) = Scalar.eval (CanonicalData.weight (gramOrigin h).1) *
      star (Scalar.eval (core (gramOrigin h).2.1)) * Scalar.eval (core (gramOrigin h).2.2) := by
  rw [← gram_weight_checked, Scalar.eval_mul, ← gram_pair_checked,
    Scalar.eval_mul, Scalar.eval_conj]
  ring

theorem local_gram_evaluation (j : Fin 14) (p q : Fin 4) :
    Scalar.eval (gram (gramIndex j (localCore j p) (localCore j q))) =
      Scalar.eval (CanonicalData.weight j) * star (Scalar.eval (core (localCore j p))) *
        Scalar.eval (core (localCore j q)) := by
  have h := gram_evaluation (gramIndex j (localCore j p) (localCore j q))
  simpa only [gramIndex_origin] using h

theorem phase_pair_evaluation (p q : Fin 20) :
    Scalar.eval (phase (phaseDifference p q)) =
      star (Scalar.eval (phase p)) * Scalar.eval (phase q) := by
  have h : Scalar.mul (Scalar.conj (phase p)) (phase q) = phase (phaseDifference p q) :=
    funext (phase_pair_check p q)
  rw [← h, Scalar.eval_mul, Scalar.eval_conj]

theorem term_complex_eq_factored (j : Fin 14) :
    complexPolynomial (termReflectedPolynomial j) =
      SOS.factoredGramExpand
        (fun p q : Fin 4 => Scalar.eval (gram (gramIndex j (localCore j p) (localCore j q))))
        (fun p q : Fin 20 => Scalar.eval (phase (phaseDifference p q))) (localTerms j) :=
  term_complex_eq_factored_of_mul Scalar.eval_mul j

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (a b : Fin 2 → unitary R)
  (ha : ∀ i, a i ^ 5 = 1) (hb : ∀ i, b i ^ 5 = 1)
  (hab : ∀ i j, Commute (a i) (b j))

include ha hb hab in
theorem termReflected_evaluation (j : Fin 14) :
    SOS.evaluate a b (complexPolynomial (termReflectedPolynomial j)) =
      (weightValue j : ℂ) •
        (star (SOS.realizingPolynomial a b j) * SOS.realizingPolynomial a b j +
          SOS.realizingPolynomial a b j * star (SOS.realizingPolynomial a b j)) :=
  termReflected_evaluation_of Scalar.eval_mul local_gram_evaluation phase_pair_evaluation
    phasePolynomial_eq_canonical a b ha hb hab j

include ha hb hab in
theorem reflected_sos_evaluation :
    SOS.evaluate a b (complexPolynomial reflectedPolynomial) =
      ∑ j : Fin 14, (weightValue j : ℂ) •
        (star (SOS.realizingPolynomial a b j) * SOS.realizingPolynomial a b j +
          SOS.realizingPolynomial a b j * star (SOS.realizingPolynomial a b j)) :=
  reflected_sos_evaluation_of Scalar.eval_mul local_gram_evaluation phase_pair_evaluation
    phasePolynomial_eq_canonical a b ha hb hab feature_expansion_checked

end
end CGLMP5.SOSFinite
