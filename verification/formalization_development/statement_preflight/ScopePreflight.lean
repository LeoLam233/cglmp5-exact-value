import CGLMP5.LowerValue
import CGLMP5.OperatorUpper
import CGLMP5.OperatorRoot

/-! Development statement preflight only. The upper bound is an explicit hypothesis here;
this file does not assert the pending unconditional SOS or replace the production theorem. -/
noncomputable section
open scoped ComplexOrder
namespace CGLMP5.StatementPreflight
universe u v

set_option pp.universes true in
#check @CGLMP5.tensor_povm_bound_of_unitary_bound
set_option pp.universes true in
#check @CGLMP5.Strategy
set_option pp.universes true in
#check @CGLMP5.mu_mem_quantumValues
set_option pp.universes true in
#check @CGLMP5.Strategy.lift

-- Independent local universes are accepted without dimension, countability, or state restrictions.
example {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (hupper : ∀ a b : Fin 2 → unitary (Op (HTensor (DilationSpace H) (DilationSpace K))),
      (∀ i, a i ^ 5 = 1) → (∀ i, b i ^ 5 = 1) →
      (∀ i j, Commute (a i) (b j)) →
      SOS.bell (zeta ^ 4) a b ≤ (mu : ℂ) • 1)
    (φ : State (HTensor H K)) (A : Setting → POVM H) (B : Setting → POVM K) :
    cglmp (jointProbability φ A B) ≤ mu :=
  tensor_povm_bound_of_unitary_bound mu (zeta ^ 4) zeta_four_unitary
    zeta_four_fifth zeta_four_sum hupper φ A B

-- The fixed physical witness has literally the two requested local five-dimensional spaces.
example : Attainment.explicitStrategy.Alice = EuclideanSpace ℂ (Fin 5) := rfl
example : Attainment.explicitStrategy.Bob = EuclideanSpace ℂ (Fin 5) := rfl
example : Attainment.H25 = EuclideanSpace ℂ (Fin 5 × Fin 5) := rfl
example : (Attainment.explicitStrategy.lift.{u,v}).value = mu := by
  rw [Strategy.lift_value, Attainment.explicitStrategy_value]

-- Exact final supremum assembly type-checks at arbitrary independent universes.
example (hu : ∀ S : Strategy.{u,v}, S.value ≤ mu) :
    IsGreatest (quantumValues.{u,v}) mu := by
  refine ⟨mu_mem_quantumValues, ?_⟩
  rintro q ⟨S, rfl⟩
  exact hu S

example (hu : ∀ S : Strategy.{u,v}, S.value ≤ mu) :
    sSup (quantumValues.{u,v}) = mu ∧
    sextic mu = 0 ∧ (∀ t : ℝ, sextic t = 0 → t ≤ mu) ∧
    Attainment.explicitStrategy.value = mu := by
  have hx : sSup (quantumValues.{u,v}) = mu := by
    apply supremum_of_bound_attainment mu hu
    exact mu_mem_quantumValues
  exact ⟨hx, sextic_mu, mu_largest_root, Attainment.explicitStrategy_value⟩

end CGLMP5.StatementPreflight
