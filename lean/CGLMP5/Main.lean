import CGLMP5.OperatorTheorem
import CGLMP5.LowerValue
import CGLMP5.CertificateSource

/-! # The exact CGLMP5 quantum value

These roots retain arbitrary local Hilbert spaces, arbitrary local five-outcome
POVMs, and every normalized positive state on their completed tensor product.
The source-binding module is imported as a mandatory artifact gate.
-/

namespace CGLMP5
universe u v

/-- Every strategy in the complete, unrestricted local tensor-product model obeys the bound. -/
theorem strategy_value_le_mu (S : Strategy.{u,v}) : S.value ≤ mu :=
  tensor_povm_upper S.state S.aliceMeasurements S.bobMeasurements

/-- The supremum is an attained maximum, with no finite-dimensional restriction on the set. -/
theorem quantumValues_isGreatest : IsGreatest (quantumValues.{u,v}) mu := by
  refine ⟨mu_mem_quantumValues, ?_⟩
  rintro q ⟨S, rfl⟩
  exact strategy_value_le_mu S

/-- The published exact-value conclusion, for every pair of Hilbert-space universes. -/
theorem quantumValue_exact : sSup (quantumValues.{u,v}) = mu := by
  apply supremum_of_bound_attainment mu strategy_value_le_mu
  exact mu_mem_quantumValues

/-- The exact maximum is the largest real root of the literal published sextic. -/
theorem cglmp5_exact :
    sSup (quantumValues.{u,v}) = mu ∧
    sextic mu = 0 ∧
    (∀ t : ℝ, sextic t = 0 → t ≤ mu) ∧
    Attainment.explicitStrategy.value = mu := by
  exact ⟨quantumValue_exact, sextic_mu, mu_largest_root, Attainment.explicitStrategy_value⟩

end CGLMP5
