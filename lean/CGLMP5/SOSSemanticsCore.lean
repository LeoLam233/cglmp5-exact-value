import CGLMP5.SOSGramSemantics
import CGLMP5.SOSFeatureSemantics
import CGLMP5.SOSScalarPolynomial
import CGLMP5.SOSRealization
import CGLMP5.Positivity

/-! # Independent semantic core for the compressed SOS expansion

The finite certificates are explicit parameters here. The final wrapper supplies every one
from kernel-checked source, scalar, phase, and feature lemmas; no parameter is left on a final root.
-/
namespace CGLMP5.SOSFinite
noncomputable section

def termReflectedPolynomial (j : Fin 14) : List (Word × Scalar) :=
  (computedFeatures j).map fun t => (t.1, featureValue t.2)

theorem term_complex_eq_factored_of_mul
    (hMul : ∀ c d : Scalar, Scalar.eval (Scalar.mul c d) = Scalar.eval c * Scalar.eval d)
    (j : Fin 14) :
    complexPolynomial (termReflectedPolynomial j) =
      SOS.factoredGramExpand
        (fun p q : Fin 4 => Scalar.eval (gram (gramIndex j (localCore j p) (localCore j q))))
        (fun p q : Fin 20 => Scalar.eval (phase (phaseDifference p q))) (localTerms j) := by
  simp only [complexPolynomial, termReflectedPolynomial, computedFeatures,
    SOS.factoredGramExpand, featureValue, List.map_flatMap, List.map_map,
    Function.comp_def, List.map_cons, List.map_nil, hMul]

variable
    (hMul : ∀ c d : Scalar, Scalar.eval (Scalar.mul c d) = Scalar.eval c * Scalar.eval d)
    (hGram : ∀ (j : Fin 14) (p q : Fin 4),
      Scalar.eval (gram (gramIndex j (localCore j p) (localCore j q))) =
        Scalar.eval (CanonicalData.weight j) * star (Scalar.eval (core (localCore j p))) *
          Scalar.eval (core (localCore j q)))
    (hPhase : ∀ p q : Fin 20, Scalar.eval (phase (phaseDifference p q)) =
      star (Scalar.eval (phase p)) * Scalar.eval (phase q))
    (hCanonical : ∀ j : Fin 14,
      SOS.phasePolynomial (fun p => Scalar.eval (core (localCore j p)))
        (fun p => Scalar.eval (phase p)) (localTerms j) = complexPolynomial (CanonicalData.polynomial j))
    {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    (a b : Fin 2 → unitary R)
    (ha : ∀ i, a i ^ 5 = 1) (hb : ∀ i, b i ^ 5 = 1)
    (hab : ∀ i j, Commute (a i) (b j))

include hMul hGram hPhase hCanonical ha hb hab in
theorem termReflected_evaluation_of (j : Fin 14) :
    SOS.evaluate a b (complexPolynomial (termReflectedPolynomial j)) =
      (weightValue j : ℂ) •
        (star (SOS.realizingPolynomial a b j) * SOS.realizingPolynomial a b j +
          SOS.realizingPolynomial a b j * star (SOS.realizingPolynomial a b j)) := by
  rw [term_complex_eq_factored_of_mul hMul]
  rw [SOS.evaluate_factoredGramExpand a b ha hb hab
    (Scalar.eval (CanonicalData.weight j))
    (fun p => Scalar.eval (core (localCore j p))) (fun p => Scalar.eval (phase p))
    _ _ (hGram j) hPhase]
  rw [hCanonical, weight_evaluation]
  rfl

include hMul hGram hPhase hCanonical ha hb hab in
theorem reflected_sos_evaluation_of
    (hExpansion : ∀ j : Fin 14,
      computedFeatures j = (indexedFeatures j).map (fun t => (wordAt t.1, t.2))) :
    SOS.evaluate a b (complexPolynomial reflectedPolynomial) =
      ∑ j : Fin 14, (weightValue j : ℂ) •
        (star (SOS.realizingPolynomial a b j) * SOS.realizingPolynomial a b j +
          SOS.realizingPolynomial a b j * star (SOS.realizingPolynomial a b j)) := by
  have hpoly : complexPolynomial reflectedPolynomial =
      (List.finRange 14).flatMap fun j => complexPolynomial (termReflectedPolynomial j) := by
    simp only [complexPolynomial, reflectedPolynomial, expandedFeatures,
      allIndexedFeatures, List.map_flatMap, List.map_map, Function.comp_def,
      termReflectedPolynomial, hExpansion]
  rw [hpoly, SOS.evaluate_finRange_flatMap]
  apply Finset.sum_congr rfl
  intro j _
  exact termReflected_evaluation_of hMul hGram hPhase hCanonical a b ha hb hab j

end
end CGLMP5.SOSFinite
