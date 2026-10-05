import CGLMP5.Measurements
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-! # Bounded operators, measurements, and arbitrary positive states

There are no finite-dimensionality, separability, or normality assumptions in this file.
-/

noncomputable section

open scoped ComplexOrder
open ContinuousLinearMap

namespace CGLMP5

/-- The algebra of all bounded operators on a complex Hilbert space. -/
abbrev Op (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] := H →L[ℂ] H

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A five-outcome POVM on an arbitrary complex Hilbert space. -/
structure POVM (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  effect : Fin 5 → Op H
  nonneg : ∀ a, 0 ≤ effect a
  sum_one : ∑ a, effect a = 1

/-- A normalized positive complex-linear functional, including nonnormal states. -/
structure State (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  functional : Op H →ₚ[ℂ] ℂ
  normalized : functional 1 = 1

namespace State

/-- The real expectation, defined for every bounded operator. -/
def expect (φ : State H) (T : Op H) : ℝ := (φ.functional T).re

@[simp] theorem expect_one (φ : State H) : φ.expect 1 = 1 := by
  simp [expect, φ.normalized]

theorem expect_le_of_le (φ : State H) {S T : Op H} (h : S ≤ T) :
    φ.expect S ≤ φ.expect T := (Complex.le_def.mp (φ.functional.monotone h)).1

theorem expect_le_of_operator_bound (φ : State H) {B : Op H} {μ : ℝ}
    (h : B ≤ (μ : ℂ) • (1 : Op H)) : φ.expect B ≤ μ := by
  have h' := φ.expect_le_of_le h
  simpa [expect, map_smul, φ.normalized] using h'

end State

/-- Finite nonnegative anticommutator sums are positive bounded operators. -/
theorem anticommutator_sum_nonneg {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (R : ι → Op H) (hd : ∀ j, 0 ≤ d j) :
    0 ≤ ∑ j, (d j : ℂ) • (star (R j) * R j + R j * star (R j)) := by
  apply Finset.sum_nonneg
  intro j _
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  apply ContinuousLinearMap.IsPositive.smul_of_nonneg
  · exact (isPositive_adjoint_comp_self (R j)).add (isPositive_self_comp_adjoint (R j))
  · simpa [Complex.le_def] using hd j

/-- An exact SOS identity gives the operator upper bound in every Hilbert dimension. -/
theorem operator_bound_of_sos {ι : Type*} [Fintype ι]
    (μ : ℝ) (B : Op H) (d : ι → ℝ) (R : ι → Op H)
    (hd : ∀ j, 0 ≤ d j)
    (identity : (μ : ℂ) • (1 : Op H) - B =
      ∑ j, (d j : ℂ) • (star (R j) * R j + R j * star (R j))) :
    B ≤ (μ : ℂ) • (1 : Op H) := by
  rw [← sub_nonneg, identity]
  exact anticommutator_sum_nonneg d R hd

/-- The SOS upper bound applies to every normalized positive state. -/
theorem state_bound_of_sos {ι : Type*} [Fintype ι]
    (φ : State H) (μ : ℝ) (B : Op H) (d : ι → ℝ) (R : ι → Op H)
    (hd : ∀ j, 0 ≤ d j)
    (identity : (μ : ℂ) • (1 : Op H) - B =
      ∑ j, (d j : ℂ) • (star (R j) * R j + R j * star (R j))) :
    φ.expect B ≤ μ :=
  φ.expect_le_of_operator_bound (operator_bound_of_sos μ B d R hd identity)

/-- Compression is a positive linear map. It is not asserted to be multiplicative. -/
def compression (J : H →L[ℂ] K) : Op K →ₚ[ℂ] Op H :=
  PositiveLinearMap.mk₀
    { toFun := fun T => J.adjoint ∘L T ∘L J
      map_add' := by intros; simp [comp_add, add_comp]
      map_smul' := by intros; simp [comp_smul, smul_comp] }
    (fun T hT => ContinuousLinearMap.nonneg_iff_isPositive.mpr
      ((ContinuousLinearMap.nonneg_iff_isPositive.mp hT).adjoint_conj J))

@[simp] theorem compression_apply (J : H →L[ℂ] K) (T : Op K) :
    compression J T = J.adjoint ∘L T ∘L J := rfl

@[simp] theorem compression_one (J : H →L[ℂ] K)
    (hJ : J.adjoint ∘L J = ContinuousLinearMap.id ℂ H) :
    compression J 1 = 1 := by
  change J.adjoint ∘L (ContinuousLinearMap.id ℂ K) ∘L J = ContinuousLinearMap.id ℂ H
  simpa only [comp_id, id_comp] using hJ

/-- A single isometry induces a state on the larger bounded-operator algebra. -/
def State.pullback (φ : State H) (J : H →L[ℂ] K)
    (hJ : J.adjoint ∘L J = ContinuousLinearMap.id ℂ H) : State K where
  functional := φ.functional.comp (compression J)
  normalized := by simp [PositiveLinearMap.comp_apply, compression_one J hJ, φ.normalized]

@[simp] theorem State.pullback_expect (φ : State H) (J : H →L[ℂ] K)
    (hJ : J.adjoint ∘L J = ContinuousLinearMap.id ℂ H) (T : Op K) :
    (φ.pullback J hJ).expect T = φ.expect (compression J T) := rfl

/-- Every PVM is a POVM in the same arbitrary Hilbert space. -/
def PVM.toPOVM (P : PVM (Op H)) : POVM H where
  effect := P.effect
  nonneg a := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    have h := isPositive_adjoint_comp_self (P.effect a)
    change (star (P.effect a) * P.effect a).IsPositive at h
    simpa only [P.selfadjoint, P.mul_self] using h
  sum_one := P.sum_one

/-- A unit vector supplies a normalized positive state; the general state is not restricted
  to states of this form. -/
def State.vector (ψ : H) (hψ : inner ℂ ψ ψ = 1) : State H where
  functional := PositiveLinearMap.mk₀
    { toFun := fun T => inner ℂ ψ (T ψ)
      map_add' := by intros; simp [inner_add_right]
      map_smul' := by intros; simp [inner_smul_right] }
    (fun T hT => (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).inner_nonneg_right ψ)
  normalized := hψ

@[simp] theorem State.vector_expect (ψ : H) (hψ : inner ℂ ψ ψ = 1) (T : Op H) :
    (State.vector ψ hψ).expect T = (inner ℂ ψ (T ψ)).re := rfl

end CGLMP5
