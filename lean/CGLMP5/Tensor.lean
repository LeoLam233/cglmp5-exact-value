import CGLMP5.Operator
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.Algebra.LinearMapCompletion

/-! # The completed Hilbert tensor product

The completion is explicit. In particular, no completeness assumption is imposed on the
algebraic tensor product, which would exclude general infinite-dimensional local spaces.
-/

noncomputable section

open ContinuousLinearMap
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace CGLMP5

abbrev HTensor (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  Completion (TensorProduct ℂ H K)

variable {E F G H E' G' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup G'] [InnerProductSpace ℂ G']

/-- Elementary tensors in the completed Hilbert tensor product. -/
def tensorPure (x : E) (y : G) : HTensor E G := (x ⊗ₜ[ℂ] y : TensorProduct ℂ E G)

/-- Tensor product of bounded maps, extended to the Hilbert completions. -/
def tensorMap (f : E →L[ℂ] F) (g : G →L[ℂ] H) : HTensor E G →L[ℂ] HTensor F H :=
  (TensorProduct.mapL f g).completion

@[simp] theorem tensorMap_coe (f : E →L[ℂ] F) (g : G →L[ℂ] H)
    (x : TensorProduct ℂ E G) :
    tensorMap f g (x : HTensor E G) = (TensorProduct.mapL f g x : HTensor F H) := by
  exact completion_apply_coe _ _

@[simp] theorem tensorMap_pure (f : E →L[ℂ] F) (g : G →L[ℂ] H) (x : E) (y : G) :
    tensorMap f g (tensorPure x y) = tensorPure (f x) (g y) := by
  simp [tensorPure, TensorProduct.mapL_tmul]

/-- Equality of bounded maps out of a completed tensor can be checked on elementary tensors. -/
theorem tensor_ext {L : Type*} [NormedAddCommGroup L] [NormedSpace ℂ L]
    {f g : HTensor E G →L[ℂ] L}
    (h : ∀ x y, f (tensorPure x y) = g (tensorPure x y)) : f = g := by
  apply DFunLike.ext'
  apply Completion.denseRange_coe.equalizer f.continuous g.continuous
  funext z
  change f (z : HTensor E G) = g (z : HTensor E G)
  induction z using TensorProduct.induction_on with
  | zero => simp [Completion.coe_zero]
  | tmul x y => exact h x y
  | add x y hx hy => simpa only [Completion.coe_add, map_add, hx, hy]

@[simp] theorem tensorMap_id :
    tensorMap (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ G) =
      ContinuousLinearMap.id ℂ (HTensor E G) := by
  apply tensor_ext
  intro x y
  simp

theorem tensorMap_comp (f₁ : E →L[ℂ] F) (f₂ : E' →L[ℂ] E)
    (g₁ : G →L[ℂ] H) (g₂ : G' →L[ℂ] G) :
    tensorMap (f₁ ∘L f₂) (g₁ ∘L g₂) = tensorMap f₁ g₁ ∘L tensorMap f₂ g₂ := by
  apply tensor_ext
  intro x y
  simp

@[simp] theorem tensorMap_one : tensorMap (1 : Op E) (1 : Op G) = 1 :=
  tensorMap_id

theorem tensorMap_mul (f₁ f₂ : Op E) (g₁ g₂ : Op G) :
    tensorMap (f₁ * f₂) (g₁ * g₂) = tensorMap f₁ g₁ * tensorMap f₂ g₂ :=
  tensorMap_comp _ _ _ _

@[simp] theorem tensorPure_zero_left (y : G) : tensorPure (0 : E) y = 0 := by
  simp [tensorPure]

@[simp] theorem tensorPure_zero_right (x : E) : tensorPure x (0 : G) = 0 := by
  simp [tensorPure]

@[simp] theorem tensorPure_add_left (x y : E) (z : G) :
    tensorPure (x + y) z = tensorPure x z + tensorPure y z := by
  simp [tensorPure, TensorProduct.add_tmul, Completion.coe_add]

@[simp] theorem tensorPure_add_right (x : E) (y z : G) :
    tensorPure x (y + z) = tensorPure x y + tensorPure x z := by
  simp [tensorPure, TensorProduct.tmul_add, Completion.coe_add]

@[simp] theorem tensorPure_smul_left (c : ℂ) (x : E) (y : G) :
    tensorPure (c • x) y = c • tensorPure x y := by
  simp only [tensorPure, ← TensorProduct.smul_tmul', Completion.coe_smul]

@[simp] theorem tensorPure_smul_right (c : ℂ) (x : E) (y : G) :
    tensorPure x (c • y) = c • tensorPure x y := by
  simp only [tensorPure, TensorProduct.tmul_smul, Completion.coe_smul]

@[simp] theorem tensorMap_zero_left (g : G →L[ℂ] H) : tensorMap (0 : E →L[ℂ] F) g = 0 := by
  apply tensor_ext
  intro x y
  simp

@[simp] theorem tensorMap_zero_right (f : E →L[ℂ] F) : tensorMap f (0 : G →L[ℂ] H) = 0 := by
  apply tensor_ext
  intro x y
  simp

theorem tensorMap_add_left (f₁ f₂ : E →L[ℂ] F) (g : G →L[ℂ] H) :
    tensorMap (f₁ + f₂) g = tensorMap f₁ g + tensorMap f₂ g := by
  apply tensor_ext
  intro x y
  simp

theorem tensorMap_add_right (f : E →L[ℂ] F) (g₁ g₂ : G →L[ℂ] H) :
    tensorMap f (g₁ + g₂) = tensorMap f g₁ + tensorMap f g₂ := by
  apply tensor_ext
  intro x y
  simp

theorem tensorMap_smul_left (c : ℂ) (f : E →L[ℂ] F) (g : G →L[ℂ] H) :
    tensorMap (c • f) g = c • tensorMap f g := by
  apply tensor_ext
  intro x y
  simp

theorem tensorMap_smul_right (c : ℂ) (f : E →L[ℂ] F) (g : G →L[ℂ] H) :
    tensorMap f (c • g) = c • tensorMap f g := by
  apply tensor_ext
  intro x y
  simp

/-- Bounded operators on opposite tensor factors commute. -/
theorem tensorMap_cross_commute (f : Op E) (g : Op G) :
    Commute (tensorMap f (1 : Op G)) (tensorMap (1 : Op E) g) := by
  show tensorMap f 1 * tensorMap 1 g = tensorMap 1 g * tensorMap f 1
  rw [← tensorMap_mul, ← tensorMap_mul]
  simp

section Adjoint
variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] [CompleteSpace H]

/-- Adjoint compatibility proved on the dense algebraic tensor product, without falsely
  assuming that algebraic tensor product is complete. -/
@[simp] theorem tensorMap_adjoint (f : E →L[ℂ] F) (g : G →L[ℂ] H) :
    (tensorMap f g).adjoint = tensorMap f.adjoint g.adjoint := by
  symm
  apply (eq_adjoint_iff _ _).mpr
  have ha : ∀ (x : TensorProduct ℂ F H) (y : TensorProduct ℂ E G),
      inner ℂ (tensorMap f.adjoint g.adjoint (x : HTensor F H)) (y : HTensor E G) =
      inner ℂ (x : HTensor F H) (tensorMap f g (y : HTensor E G)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => intro y; simp [Completion.coe_zero]
    | tmul x₁ x₂ =>
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp [Completion.coe_zero]
      | tmul y₁ y₂ =>
        simp only [tensorMap_coe, TensorProduct.mapL_tmul, Completion.inner_coe,
          TensorProduct.inner_tmul, adjoint_inner_left]
      | add y z hy hz =>
        simp only [Completion.coe_add, map_add, inner_add_right, hy, hz]
    | add x z hx hz =>
      intro y
      simp only [Completion.coe_add, map_add, inner_add_left, hx y, hz y]
  intro x y
  exact Completion.induction_on₂ x y (isClosed_eq (by fun_prop) (by fun_prop)) ha

/-- Tensor products of isometries remain isometric after completion. -/
theorem tensorMap_isometry (J : E →L[ℂ] F) (K : G →L[ℂ] H)
    (hJ : J.adjoint ∘L J = ContinuousLinearMap.id ℂ E)
    (hK : K.adjoint ∘L K = ContinuousLinearMap.id ℂ G) :
    (tensorMap J K).adjoint ∘L tensorMap J K = ContinuousLinearMap.id ℂ (HTensor E G) := by
  rw [tensorMap_adjoint, ← tensorMap_comp, hJ, hK, tensorMap_id]

/-- Joint compression factors into the two local compressions. This statement deliberately
  does not assert multiplicativity of same-party compression. -/
theorem tensor_compression (J : E →L[ℂ] F) (K : G →L[ℂ] H) (A : Op F) (B : Op H) :
    compression (tensorMap J K) (tensorMap A B) =
      tensorMap (compression J A) (compression K B) := by
  simp only [compression_apply, tensorMap_adjoint]
  rw [← tensorMap_comp, ← tensorMap_comp]

end Adjoint


section TensorMeasurements
variable [CompleteSpace E] [CompleteSpace G]

theorem tensorMap_sum_left {ι : Type*} (s : Finset ι) (f : ι → Op E) (g : Op G) :
    tensorMap (∑ i ∈ s, f i) g = ∑ i ∈ s, tensorMap (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, tensorMap_add_left, ih]

theorem tensorMap_sum_right {ι : Type*} (s : Finset ι) (f : Op E) (g : ι → Op G) :
    tensorMap f (∑ i ∈ s, g i) = ∑ i ∈ s, tensorMap f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, tensorMap_add_right, ih]

/-- Alice's local PVM acting on the completed tensor product. -/
def PVM.tensorLeft (P : PVM (Op E)) : PVM (Op (HTensor E G)) where
  effect a := tensorMap (P.effect a) (1 : Op G)
  selfadjoint a := by
    change (tensorMap (P.effect a) (1 : Op G)).adjoint = _
    rw [tensorMap_adjoint, adjoint_one]
    change tensorMap (star (P.effect a)) (1 : Op G) = _
    rw [P.selfadjoint]
  mul_eq a b := by
    rw [← tensorMap_mul, one_mul, P.mul_eq]
    split_ifs <;> simp
  sum_one := by
    rw [← tensorMap_sum_left, P.sum_one, tensorMap_one]

/-- Bob's local PVM acting on the completed tensor product. -/
def PVM.tensorRight (P : PVM (Op G)) : PVM (Op (HTensor E G)) where
  effect a := tensorMap (1 : Op E) (P.effect a)
  selfadjoint a := by
    change (tensorMap (1 : Op E) (P.effect a)).adjoint = _
    rw [tensorMap_adjoint, adjoint_one]
    change tensorMap (1 : Op E) (star (P.effect a)) = _
    rw [P.selfadjoint]
  mul_eq a b := by
    rw [← tensorMap_mul, one_mul, P.mul_eq]
    split_ifs <;> simp
  sum_one := by
    rw [← tensorMap_sum_right, P.sum_one, tensorMap_one]

end TensorMeasurements

end CGLMP5
