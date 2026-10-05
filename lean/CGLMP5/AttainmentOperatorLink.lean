import CGLMP5.TensorFinite
import CGLMP5.AttainmentFourier
import CGLMP5.AttainmentMatrixDefs

noncomputable section
open scoped InnerProductSpace Matrix Kronecker
open ContinuousLinearMap

namespace CGLMP5

/-- The bounded matrix operator on Euclidean space. -/
abbrev matrixOp {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    Op (EuclideanSpace ℂ n) := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A

/-- Standard product-basis entries of the genuine bounded matrix operator. -/
theorem matrixOperator_single {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (i j : n) :
    matrixOp A (EuclideanSpace.single j 1) i = A i j := by
  change (A *ᵥ Pi.single j 1) i = A i j
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Kronecker matrices represent tensor products on the full Hilbert tensor space. -/
theorem tensorEuclideanEquiv_operator_kronecker {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    (tensorEuclideanEquiv m n).conjStarAlgEquiv
      (tensorMap (matrixOp A) (matrixOp B)) =
      matrixOp (A ⊗ₖ B) := by
  apply ContinuousLinearMap.coe_inj.mp
  apply (EuclideanSpace.basisFun (m × n) ℂ).toBasis.ext
  intro p
  obtain ⟨i,j⟩ := p
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change (tensorEuclideanEquiv m n).conjStarAlgEquiv
      (tensorMap (matrixOp A) (matrixOp B))
      (EuclideanSpace.single (i,j) 1) =
    matrixOp (A ⊗ₖ B) (EuclideanSpace.single (i,j) 1)
  apply PiLp.ext
  intro p
  obtain ⟨k,l⟩ := p
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    tensorEuclideanEquiv_map_single, matrixOperator_single]
  rfl

namespace Attainment

/-- Each entry of each physical rank-one Fourier projector matches the frozen matrix formula. -/
theorem localProjection_single (r : Fin 4) (a i j : Fin 5) :
    localProjection r a (EuclideanSpace.single j 1) i = localMatrix r a i j := by
  have hs : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
  simp only [localProjection, InnerProductSpace.rankOne_apply, EuclideanSpace.inner_single_right,
    one_mul, PiLp.smul_apply]
  change star ((s : ℂ)/5 * phase (phaseExponent r a j)) *
      ((s : ℂ)/5 * phase (phaseExponent r a i)) =
    phase (phaseExponent r a i) * star (phase (phaseExponent r a j)) / 5
  simp only [star_mul, star_div₀, Complex.star_def, map_ofNat, Complex.conj_ofReal]
  calc
    _ = (s : ℂ)^2 / 25 *
      (phase (phaseExponent r a i) * star (phase (phaseExponent r a j))) := by
        simp only [Complex.star_def]
        ring
    _ = _ := by rw [hs]; simp only [Complex.star_def]; ring

/-- The local bounded operator is exactly the matrix operator, rather than just an expectation. -/
theorem localProjection_eq_matrix (r : Fin 4) (a : Fin 5) :
    localProjection r a = matrixOp (localMatrix r a) := by
  apply ContinuousLinearMap.coe_inj.mp
  apply (EuclideanSpace.basisFun (Fin 5) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change localProjection r a (EuclideanSpace.single j 1) =
    matrixOp (localMatrix r a) (EuclideanSpace.single j 1)
  apply PiLp.ext
  intro i
  rw [localProjection_single, matrixOperator_single]

/-- The full 25-dimensional physical joint projector is the corresponding Kronecker matrix. -/
theorem jointProjection_eq_matrix (r t : Fin 4) (a b : Fin 5) :
    (tensorEuclideanEquiv (Fin 5) (Fin 5)).conjStarAlgEquiv
      (tensorMap (localProjection r a) (localProjection t b)) =
      matrixOp (localMatrix r a ⊗ₖ localMatrix t b) := by
  rw [localProjection_eq_matrix, localProjection_eq_matrix, tensorEuclideanEquiv_operator_kronecker]

end Attainment
end CGLMP5
