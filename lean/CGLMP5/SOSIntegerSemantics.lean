import CGLMP5.SOSIntegerDataSoundness
import CGLMP5.SOSIntegerResidualDefinitions
import CGLMP5.SOSDenominatorSemantics
import CGLMP5.SOSScalarPolynomial

namespace CGLMP5.SOSFinite

theorem sumScalars_apply (ss : List Scalar) (k : Fin 24) :
    sumScalars ss k = (ss.map fun s => s k).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [Scalar.add, ih]

theorem featureValue_as_fraction (f : Feature) (k : Fin 24) :
    featureValue f k =
      (Scalar.mulNumerator (gramNumerator f.1) (phaseNumerator f.2) k : ℚ) /
        (gramDenominator f.1 * phaseDenominator f.2 : ℕ) := by
  rw [featureValue, gram_as_canonical, phase_as_canonical, Scalar.mul_ofCanonical]

/-- Rational normalization is replaced by one checked common integer denominator. -/
theorem fiberValue_as_fraction (i : Fin 273) (k : Fin 24)
    (hdiv : ∀ f ∈ fiber i,
      commonDenominator i % (gramDenominator f.1 * phaseDenominator f.2) = 0) :
    fiberValue i k = (integerNumerator i k : ℚ) / commonDenominator i := by
  let terms : List (ℤ × ℕ) := (fiber i).map fun f =>
    (Scalar.mulNumerator (gramNumerator f.1) (phaseNumerator f.2) k,
      gramDenominator f.1 * phaseDenominator f.2)
  have hpos : ∀ t ∈ terms, 0 < t.2 := by
    intro t ht
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ht
    exact Nat.mul_pos (all_denominators_positive.1 f.1)
      (all_denominators_positive.2.1 f.2)
  have hd : ∀ t ∈ terms, commonDenominator i % t.2 = 0 := by
    intro t ht
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ht
    exact hdiv f hf
  have h := list_common_denominator terms (commonDenominator i)
    (all_denominators_positive.2.2.2 i) hpos hd
  simpa only [terms, fiberValue, sumScalars_apply, List.map_map, Function.comp_def,
    featureValue_as_fraction, integerNumerator] using h

/-- A certified integer cross-product proves the intended rational scalar coordinate equality. -/
theorem fiberValue_eq_target_of_integer (i : Fin 273)
    (hdiv : ∀ f ∈ fiber i,
      commonDenominator i % (gramDenominator f.1 * phaseDenominator f.2) = 0)
    (hint : ∀ k : Fin 24,
      integerNumerator i k * (targetDenominator i : ℤ) =
        targetNumerator i k * (commonDenominator i : ℤ)) :
    fiberValue i = targetAt i := by
  funext k
  rw [fiberValue_as_fraction i k hdiv, target_as_canonical]
  change (integerNumerator i k : ℚ) / commonDenominator i =
    (targetNumerator i k : ℚ) / targetDenominator i
  apply (div_eq_div_iff ?_ ?_).mpr
  · exact_mod_cast hint k
  · exact_mod_cast Nat.ne_of_gt (all_denominators_positive.2.2.2 i)
  · exact_mod_cast Nat.ne_of_gt (all_denominators_positive.2.2.1 i)

end CGLMP5.SOSFinite
