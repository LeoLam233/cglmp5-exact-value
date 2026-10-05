import CGLMP5.Tensor

/-! # Finite full-space adapter

The full product basis is retained. This adapter identifies the completed tensor product of
finite Euclidean spaces with Euclidean space on the product index, without any diagonal compression.
-/

noncomputable section
open scoped TensorProduct InnerProductSpace
open UniformSpace ContinuousLinearMap

namespace CGLMP5

variable (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The complete product orthonormal basis, with every pair of local coordinates. -/
def tensorEuclideanBasis : OrthonormalBasis (m × n) ℂ
    (TensorProduct ℂ (EuclideanSpace ℂ m) (EuclideanSpace ℂ n)) :=
  (EuclideanSpace.basisFun m ℂ).tensorProduct (EuclideanSpace.basisFun n ℂ)

/-- The product-basis coordinate map, extended from algebraic tensors to their completion. -/
def tensorEuclideanMap : HTensor (EuclideanSpace ℂ m) (EuclideanSpace ℂ n) →L[ℂ]
    EuclideanSpace ℂ (m × n) :=
  (tensorEuclideanBasis m n).repr.toContinuousLinearEquiv.toContinuousLinearMap.fromCompletion

@[simp] theorem tensorEuclideanMap_coe
    (x : TensorProduct ℂ (EuclideanSpace ℂ m) (EuclideanSpace ℂ n)) :
    tensorEuclideanMap m n x = (tensorEuclideanBasis m n).repr x := by
  exact fromCompletion_apply_coe _ _

theorem tensorEuclideanMap_norm (x : HTensor (EuclideanSpace ℂ m) (EuclideanSpace ℂ n)) :
    ‖tensorEuclideanMap m n x‖ = ‖x‖ := by
  exact Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop))
    (fun z => by simp [Completion.norm_coe])

/-- The full finite tensor product is isometrically equivalent to the full product-index space. -/
def tensorEuclideanEquiv : HTensor (EuclideanSpace ℂ m) (EuclideanSpace ℂ n) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ (m × n) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (tensorEuclideanMap m n).toLinearMap
      norm_map' := tensorEuclideanMap_norm m n }
    (fun v => ⟨((tensorEuclideanBasis m n).repr.symm v :
      TensorProduct ℂ (EuclideanSpace ℂ m) (EuclideanSpace ℂ n)), by simp⟩)

@[simp] theorem tensorEuclideanEquiv_coe
    (x : TensorProduct ℂ (EuclideanSpace ℂ m) (EuclideanSpace ℂ n)) :
    tensorEuclideanEquiv m n x = (tensorEuclideanBasis m n).repr x := by
  exact tensorEuclideanMap_coe m n x

@[simp] theorem tensorEuclideanEquiv_pure (x : EuclideanSpace ℂ m) (y : EuclideanSpace ℂ n)
    (i : m) (j : n) :
    tensorEuclideanEquiv m n (tensorPure x y) (i,j) = x i * y j := by
  simp [tensorPure, tensorEuclideanBasis, mul_comm]

@[simp] theorem tensorEuclideanEquiv_symm_single (i : m) (j : n) :
    (tensorEuclideanEquiv m n).symm (EuclideanSpace.single (i,j) 1) =
      tensorPure (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  apply (tensorEuclideanEquiv m n).injective
  ext p
  obtain ⟨k,l⟩ := p
  simp [tensorEuclideanEquiv_pure, EuclideanSpace.single_apply, ite_and]
  split_ifs <;> rfl

/-- Every product-basis coordinate of a tensor operator is preserved by the full-space adapter. -/
theorem tensorEuclideanEquiv_map_single (A : Op (EuclideanSpace ℂ m))
    (B : Op (EuclideanSpace ℂ n)) (i k : m) (j l : n) :
    tensorEuclideanEquiv m n
      (tensorMap A B ((tensorEuclideanEquiv m n).symm (EuclideanSpace.single (i,j) 1))) (k,l) =
      A (EuclideanSpace.single i 1) k * B (EuclideanSpace.single j 1) l := by
  rw [tensorEuclideanEquiv_symm_single, tensorMap_pure, tensorEuclideanEquiv_pure]

end CGLMP5
