import CGLMP5.SOSIndexFiberChecks
import CGLMP5.SOSIntegerSemantics

/-! Kernel-checked integer residuals imply equality in every allowed representation. -/
namespace CGLMP5.SOSFinite

def indexedScalarFeatures : List (Fin 273 × Scalar) :=
  allIndexedFeatures.map fun t => (t.1, featureValue t.2)

theorem map_filter_value {ι α β : Type*} [DecidableEq ι]
    (f : α → β) (es : List (ι × α)) (i : ι) :
    (((es.map fun t => (t.1, f t.2)).filter fun t => t.1 = i).map Prod.snd) =
      (((es.filter fun t => t.1 = i).map Prod.snd).map f) := by
  induction es with
  | nil => rfl
  | cons t es ih =>
    by_cases h : t.1 = i <;> simp [h, ih]

theorem indexed_feature_coefficient (i : Fin 273) :
    sumScalars (((indexedScalarFeatures.filter fun t => t.1 = i).map Prod.snd)) =
      fiberValue i := by
  rw [indexedScalarFeatures, map_filter_value, index_fiber_checked]
  rfl

theorem reflected_index_coefficients_of
    (hden : ∀ i, ∀ f ∈ fiber i, commonDenominator i % (gramDenominator f.1 * phaseDenominator f.2) = 0)
    (hres : ∀ i, integerResidualClaim i)
    (htarget : ∀ (i : Fin 273) (k : Fin 24), sumScalars (((targetIndexedPolynomial.filter fun t => t.1 = i).map Prod.snd)) k = targetAt i k)
    (i : Fin 273) :
    sumScalars (((indexedScalarFeatures.filter fun t => t.1 = i).map Prod.snd)) =
      sumScalars (((targetIndexedPolynomial.filter fun t => t.1 = i).map Prod.snd)) := by
  rw [indexed_feature_coefficient,
    fiberValue_eq_target_of_integer i (hden i) (hres i)]
  exact (funext (htarget i)).symm

noncomputable section
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  (a b : Fin 2 → unitary R)

/-- The complete273-word compact identity follows from kernel-checked integer coordinates. -/
theorem reflected_evaluation_eq_target_of
    (hcoeff : ∀ i,
      sumScalars (((indexedScalarFeatures.filter fun t => t.1 = i).map Prod.snd)) =
      sumScalars (((targetIndexedPolynomial.filter fun t => t.1 = i).map Prod.snd)))
    (hmap : targetIndexedPolynomial.map (fun t => (wordAt t.1, t.2)) = targetPolynomial) :
    SOS.evaluate a b (complexPolynomial reflectedPolynomial) =
      SOS.evaluate a b (complexPolynomial targetPolynomial) := by
  have h := evaluate_indexed_eq a b wordAt indexedScalarFeatures targetIndexedPolynomial
    hcoeff
  rw [← hmap]
  simpa only [complexPolynomial, reflectedPolynomial, expandedFeatures,
    indexedScalarFeatures, List.map_map, Function.comp_def] using h

end
end CGLMP5.SOSFinite
