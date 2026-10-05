import CGLMP5.AttainmentSourceHeader
import CGLMP5.AttainmentEigen
import CGLMP5.AttainmentSpectralLink
import CGLMP5.OperatorUpper
import CGLMP5.Strategy

namespace CGLMP5.Attainment
noncomputable section

/-- The normalized Schmidt vector in the completed Hilbert tensor product C^5⊗C^5. -/
def physicalVector : HTensor H5 H5 :=
  (tensorEuclideanEquiv (Fin 5) (Fin 5)).symm state

lemma physicalVector_coordinates :
    tensorEuclideanEquiv (Fin 5) (Fin 5) physicalVector = state :=
  (tensorEuclideanEquiv (Fin 5) (Fin 5)).apply_symm_apply state

lemma physicalVector_norm : ‖physicalVector‖ = 1 := by
  simpa [physicalVector] using
    ((tensorEuclideanEquiv (Fin 5) (Fin 5)).symm.norm_map state).trans state_norm

lemma physicalVector_inner : inner ℂ physicalVector physicalVector = 1 := by
  rw [inner_self_eq_norm_sq_to_K, physicalVector_norm]
  norm_num

/-- The explicit vector defines a positive normalized state on all bounded tensor operators. -/
def physicalState : State (HTensor H5 H5) := State.vector physicalVector physicalVector_inner

/-- Full physical Bell eigen-equation before taking an expectation or a compression. -/
lemma physicalVector_eigen : literalBell fullAlice fullBob physicalVector =
    (mu : ℂ) • physicalVector := by
  apply (tensorEuclideanEquiv (Fin 5) (Fin 5)).injective
  rw [map_smul, physicalVector_coordinates]
  calc
    tensorEuclideanEquiv (Fin 5) (Fin 5) (literalBell fullAlice fullBob physicalVector) =
        matrixOp matrixBell state := by
      exact congrArg (fun T : Op H25 => T state) literalBell_coordinates
    _ = (mu : ℂ) • state := state_eigen

lemma physicalState_expectation : physicalState.expect (literalBell fullAlice fullBob) = mu := by
  simp only [physicalState, State.vector_expect, physicalVector_eigen, inner_smul_right,
    physicalVector_inner, mul_one, Complex.ofReal_re]

/-- Literal probability-form attainment with the exact offsets and normalized Schmidt state. -/
theorem cglmp_attainment :
    cglmp (jointProbability physicalState (fun x => (alicePVM x).toPOVM)
      (fun y => (bobPVM y).toPOVM)) = mu := by
  rw [cglmp_eq_expect_bell, ← literalBell_tensor]
  exact physicalState_expectation

/-- A complete admissible strategy with local dimension five at both parties. -/
def explicitStrategy : Strategy.{0,0} where
  Alice := H5
  Bob := H5
  state := physicalState
  aliceMeasurements x := (alicePVM x).toPOVM
  bobMeasurements y := (bobPVM y).toPOVM

/-- The actual full tensor-product strategy attains the selected largest root. -/
theorem explicitStrategy_value : explicitStrategy.value = mu := cglmp_attainment

/-- The lower witness has both local spaces exactly C^5, with no compressed-only surrogate. -/
theorem exists_attaining_strategy : ∃ S : Strategy.{0,0}, S.value = mu :=
  ⟨explicitStrategy, explicitStrategy_value⟩

end
end CGLMP5.Attainment
