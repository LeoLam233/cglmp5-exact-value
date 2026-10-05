import CGLMP5.SOSIdentity
import CGLMP5.OperatorUpper
import CGLMP5.OperatorRoot

/-!
# The actual arbitrary-Hilbert-space upper theorem

The canonical scalar embedding, all fourteen strictly positive weights, and the
source-bound compact identity are instantiated here. No finite-dimensionality,
separability, normality, tensor-factorization of the state, or pure-state hypothesis
is present. The bounded commuting-PVM identity is independent of a tensor model;
the final POVM inequality uses the fixed-common-embedding local dilation.
-/
noncomputable section
open scoped ComplexOrder

namespace CGLMP5

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The actual unitary Bell upper bound for arbitrary bounded representations. -/
theorem bounded_unitary_upper (a b : Fin 2 → unitary (Op H))
    (ha : ∀ i, a i ^ 5 = 1) (hb : ∀ i, b i ^ 5 = 1)
    (hab : ∀ i j, Commute (a i) (b j)) :
    SOS.bell (zeta ^ 4) a b ≤ (mu : ℂ) • (1 : Op H) :=
  operator_bound_of_sos mu (SOS.bell (zeta ^ 4) a b) weightValue
    (SOS.realizingPolynomial a b) (fun j => le_of_lt (weight_positive j))
    (SOS.compact_identity a b ha hb hab)

/-- The canonical certificate polynomial evaluated in a commuting PVM representation. -/
def pvmResidual (A B : Fin 2 → PVM (Op H)) (j : Fin 14) : Op H :=
  SOS.realizingPolynomial
    (measurementUnitaries (zeta ^ 4) zeta_four_unitary A)
    (measurementUnitaries (zeta ^ 4) zeta_four_unitary B) j

/-- The actual exact SOS identity in every bounded cross-party commuting PVM model. -/
theorem commuting_pvm_sos_identity (A B : Fin 2 → PVM (Op H))
    (hcomm : ∀ x y a b, Commute ((A x).effect a) ((B y).effect b)) :
    (mu : ℂ) • (1 : Op H) - literalBell A B =
      ∑ j : Fin 14, (weightValue j : ℂ) •
        (star (pvmResidual A B j) * pvmResidual A B j +
          pvmResidual A B j * star (pvmResidual A B j)) := by
  rw [← sosBell_eq_literal (zeta ^ 4) zeta_four_unitary zeta_four_fifth
    zeta_four_sum A B hcomm]
  exact SOS.compact_identity _ _
    (measurementUnitaries_fifth (zeta ^ 4) zeta_four_unitary zeta_four_fifth A)
    (measurementUnitaries_fifth (zeta ^ 4) zeta_four_unitary zeta_four_fifth B)
    (measurementUnitaries_commute (zeta ^ 4) zeta_four_unitary A B hcomm)

/-- The literal Bell operator is bounded above in every bounded commuting PVM model. -/
theorem commuting_pvm_upper (A B : Fin 2 → PVM (Op H))
    (hcomm : ∀ x y a b, Commute ((A x).effect a) ((B y).effect b)) :
    literalBell A B ≤ (mu : ℂ) • (1 : Op H) :=
  operator_bound_of_sos mu (literalBell A B) weightValue (pvmResidual A B)
    (fun j => le_of_lt (weight_positive j)) (commuting_pvm_sos_identity A B hcomm)

/-- Every normalized positive state obeys the commuting-PVM upper bound. -/
theorem commuting_pvm_state_upper (φ : State H) (A B : Fin 2 → PVM (Op H))
    (hcomm : ∀ x y a b, Commute ((A x).effect a) ((B y).effect b)) :
    φ.expect (literalBell A B) ≤ mu :=
  φ.expect_le_of_operator_bound (commuting_pvm_upper A B hcomm)

/-- The original CGLMP5 upper bound for arbitrary local Hilbert spaces and POVMs. -/
theorem tensor_povm_upper (φ : State (HTensor H K))
    (A : Setting → POVM H) (B : Setting → POVM K) :
    cglmp (jointProbability φ A B) ≤ mu :=
  tensor_povm_bound_of_unitary_bound mu (zeta ^ 4) zeta_four_unitary
    zeta_four_fifth zeta_four_sum
    (fun a b ha hb hab => bounded_unitary_upper a b ha hb hab) φ A B

end CGLMP5
