import CGLMP5.POVMDilation
import CGLMP5.Tensor
import CGLMP5.Events

noncomputable section
open scoped ComplexOrder InnerProductSpace
open ContinuousLinearMap

namespace CGLMP5

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Joint expectations of local tensor-product POVM effects in an arbitrary positive state. -/
def jointProbability (φ : State (HTensor H K)) (A : Setting → POVM H) (B : Setting → POVM K)
    (x y : Setting) (a b : Outcome) : ℝ :=
  φ.expect (tensorMap ((A x).effect a) ((B y).effect b))

/-- The literal CGLMP Bell operator, fixed by the eight-event coefficient convention. -/
def bellOperator (A : Setting → POVM H) (B : Setting → POVM K) : Op (HTensor H K) :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    ((eventCoefficientTwo x y a b : ℂ) / 2) • tensorMap ((A x).effect a) ((B y).effect b)

theorem cglmp_eq_expect_bell (φ : State (HTensor H K))
    (A : Setting → POVM H) (B : Setting → POVM K) :
    cglmp (jointProbability φ A B) = φ.expect (bellOperator A B) := by
  simp [cglmp, jointProbability, bellOperator, State.expect, map_sum, map_smul,
    Complex.mul_re, Complex.div_re, Complex.div_im]

set_option maxHeartbeats 800000 in
/-- The enlarged state depends on one fixed pair of embeddings, and not on any setting. -/
def dilateState (φ : State (HTensor H K)) : State (HTensor (DilationSpace H) (DilationSpace K)) :=
  φ.pullback (tensorMap (commonJ (H := H)) (commonJ (H := K)))
    (tensorMap_isometry (commonJ (H := H)) (commonJ (H := K))
      (commonJ_isometry (H := H)) (commonJ_isometry (H := K)))

/-- Every joint tensor-product expectation is preserved by the single common embedding. -/
theorem jointProbability_dilate (φ : State (HTensor H K))
    (A : Setting → POVM H) (B : Setting → POVM K) (x y : Setting) (a b : Outcome) :
    jointProbability (dilateState φ) (fun x => (A x).dilate.toPOVM)
      (fun y => (B y).dilate.toPOVM) x y a b = jointProbability φ A B x y a b := by
  change (φ.pullback (tensorMap commonJ commonJ) _).expect
    (tensorMap ((A x).dilate.effect a) ((B y).dilate.effect b)) = _
  rw [State.pullback_expect, tensor_compression, POVM.dilate_compression, POVM.dilate_compression]
  rfl

/-- The entire literal functional is preserved simultaneously across all four setting pairs. -/
theorem cglmp_dilate (φ : State (HTensor H K)) (A : Setting → POVM H) (B : Setting → POVM K) :
    cglmp (jointProbability (dilateState φ) (fun x => (A x).dilate.toPOVM)
      (fun y => (B y).dilate.toPOVM)) = cglmp (jointProbability φ A B) := by
  congr 1
  funext x y a b
  exact jointProbability_dilate φ A B x y a b

/-- Universal projective bounds transfer to arbitrary local POVMs on arbitrary local Hilbert
  spaces, including nonseparable spaces and nonnormal positive states. -/
theorem povm_bound_of_pvm_bound (μ : ℝ)
    (hbound : ∀ (φ : State (HTensor (DilationSpace H) (DilationSpace K)))
      (A : Setting → PVM (Op (DilationSpace H)))
      (B : Setting → PVM (Op (DilationSpace K))),
      cglmp (jointProbability φ (fun x => (A x).toPOVM) (fun y => (B y).toPOVM)) ≤ μ)
    (φ : State (HTensor H K)) (A : Setting → POVM H) (B : Setting → POVM K) :
    cglmp (jointProbability φ A B) ≤ μ := by
  rw [← cglmp_dilate φ A B]
  exact hbound (dilateState φ) (fun x => (A x).dilate) (fun y => (B y).dilate)

end CGLMP5
