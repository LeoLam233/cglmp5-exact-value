import CGLMP5.BellBridge
import CGLMP5.POVMProbabilities

noncomputable section
open scoped ComplexOrder

namespace CGLMP5

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The unitary Bell bound applies to any bounded cross-party commuting projective representation. -/
theorem commuting_pvm_bound_of_unitary_bound (μ : ℝ) (ω : ℂ)
    (hunit : star ω * ω = 1) (hω : ω^5 = 1) (hc : 1+ω+ω^2+ω^3+ω^4 = 0)
    (hbound : ∀ a b : Fin 2 → unitary (Op H),
      (∀ i, a i^5=1) → (∀ i, b i^5=1) → (∀ i j, Commute (a i) (b j)) →
      SOS.bell ω a b ≤ (μ : ℂ) • (1 : Op H))
    (A B : Fin 2 → PVM (Op H))
    (hcomm : ∀ x y a b, Commute ((A x).effect a) ((B y).effect b)) :
    literalBell A B ≤ (μ : ℂ) • (1 : Op H) := by
  rw [← sosBell_eq_literal ω hunit hω hc A B hcomm]
  exact hbound _ _ (measurementUnitaries_fifth ω hunit hω A)
    (measurementUnitaries_fifth ω hunit hω B) (measurementUnitaries_commute ω hunit A B hcomm)

/-- The tensor-product literal Bell operator equals the commuting-representation literal Bell
  operator after lifting each party's local PVM. -/
theorem literalBell_tensor (A : Setting → PVM (Op H)) (B : Setting → PVM (Op K)) :
    literalBell (fun x => (A x).tensorLeft (G := K)) (fun y => (B y).tensorRight (E := H)) =
      bellOperator (fun x => (A x).toPOVM) (fun y => (B y).toPOVM) := by
  unfold literalBell bellOperator
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  change tensorMap ((A x).effect a) (1 : Op K) * tensorMap (1 : Op H) ((B y).effect b) = _
  rw [← tensorMap_mul, mul_one, one_mul]
  rfl

theorem tensor_pvm_bound_of_unitary_bound (μ : ℝ) (ω : ℂ)
    (hunit : star ω * ω = 1) (hω : ω^5 = 1) (hc : 1+ω+ω^2+ω^3+ω^4 = 0)
    (hbound : ∀ a b : Fin 2 → unitary (Op (HTensor H K)),
      (∀ i, a i^5=1) → (∀ i, b i^5=1) → (∀ i j, Commute (a i) (b j)) →
      SOS.bell ω a b ≤ (μ : ℂ) • (1 : Op (HTensor H K)))
    (φ : State (HTensor H K)) (A : Setting → PVM (Op H)) (B : Setting → PVM (Op K)) :
    cglmp (jointProbability φ (fun x => (A x).toPOVM) (fun y => (B y).toPOVM)) ≤ μ := by
  rw [cglmp_eq_expect_bell]
  apply φ.expect_le_of_operator_bound
  rw [← literalBell_tensor]
  apply commuting_pvm_bound_of_unitary_bound μ ω hunit hω hc hbound
  intro x y a b
  exact tensorMap_cross_commute ((A x).effect a) ((B y).effect b)

/-- A universal bounded-unitary Bell bound transfers, without a dimensional restriction, to
  every tensor-product local POVM and every normalized positive state. -/
theorem tensor_povm_bound_of_unitary_bound (μ : ℝ) (ω : ℂ)
    (hunit : star ω * ω = 1) (hω : ω^5 = 1) (hc : 1+ω+ω^2+ω^3+ω^4 = 0)
    (hbound : ∀ a b : Fin 2 → unitary (Op (HTensor (DilationSpace H) (DilationSpace K))),
      (∀ i, a i^5=1) → (∀ i, b i^5=1) → (∀ i j, Commute (a i) (b j)) →
      SOS.bell ω a b ≤ (μ : ℂ) • (1 : Op (HTensor (DilationSpace H) (DilationSpace K))))
    (φ : State (HTensor H K)) (A : Setting → POVM H) (B : Setting → POVM K) :
    cglmp (jointProbability φ A B) ≤ μ := by
  apply povm_bound_of_pvm_bound μ _ φ A B
  intro ψ P Q
  exact tensor_pvm_bound_of_unitary_bound μ ω hunit hω hc hbound ψ P Q

end CGLMP5
