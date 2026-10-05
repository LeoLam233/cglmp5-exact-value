import CGLMP5.POVMProbabilities
import Mathlib.Order.ConditionallyCompleteLattice.Basic

noncomputable section
namespace CGLMP5
universe u v

/-- The entire local tensor-product POVM model, with unrestricted local Hilbert dimensions. -/
structure Strategy where
  Alice : Type u
  Bob : Type v
  [aliceNorm : NormedAddCommGroup Alice]
  [bobNorm : NormedAddCommGroup Bob]
  [aliceInner : InnerProductSpace ℂ Alice]
  [bobInner : InnerProductSpace ℂ Bob]
  [aliceComplete : CompleteSpace Alice]
  [bobComplete : CompleteSpace Bob]
  state : State (HTensor Alice Bob)
  aliceMeasurements : Setting → POVM Alice
  bobMeasurements : Setting → POVM Bob

attribute [instance] Strategy.aliceNorm Strategy.bobNorm Strategy.aliceInner Strategy.bobInner
  Strategy.aliceComplete Strategy.bobComplete

/-- The literal CGLMP value of a bundled strategy. -/
def Strategy.value (S : Strategy) : ℝ :=
  cglmp (jointProbability S.state S.aliceMeasurements S.bobMeasurements)

/-- All values in the original tensor-product POVM model at the indicated universes. -/
def quantumValues : Set ℝ := {q | ∃ S : Strategy.{u,v}, S.value = q}

/-- A universal upper theorem and a model-attained lower theorem suffice for the exact supremum. -/
theorem supremum_of_bound_attainment (μ : ℝ)
    (hu : ∀ S : Strategy.{u,v}, S.value ≤ μ)
    (hl : ∃ S : Strategy.{u,v}, S.value = μ) : sSup (quantumValues.{u,v}) = μ := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨μ, hl⟩
    · rintro q ⟨S, rfl⟩
      exact hu S
  · apply le_csSup
    · exact ⟨μ, by rintro q ⟨S, rfl⟩; exact hu S⟩
    · exact hl

end CGLMP5
