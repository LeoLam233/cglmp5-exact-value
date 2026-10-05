import CGLMP5.SOSReflectionCore
import CGLMP5.SOSIntegerResidualChecks
import CGLMP5.SOSTargetChecks

/-! Actual checked residuals instantiate the generic coefficient-reflection proof. -/
namespace CGLMP5.SOSFinite

theorem reflected_index_coefficients (i : Fin 273) :
    sumScalars (((indexedScalarFeatures.filter fun t => t.1 = i).map Prod.snd)) =
      sumScalars (((targetIndexedPolynomial.filter fun t => t.1 = i).map Prod.snd)) :=
  reflected_index_coefficients_of denominator_divides integer_residual
    target_index_coefficients i

noncomputable section
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  (a b : Fin 2 → unitary R)

/-- The complete 273-word identity is supported by all 6552 checked coordinates. -/
theorem reflected_evaluation_eq_target :
    SOS.evaluate a b (complexPolynomial reflectedPolynomial) =
      SOS.evaluate a b (complexPolynomial targetPolynomial) :=
  reflected_evaluation_eq_target_of a b reflected_index_coefficients target_index_word_map

end
end CGLMP5.SOSFinite
