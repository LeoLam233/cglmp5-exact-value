import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin

namespace CGLMP5

/-- A five-outcome projective measurement in a unital star ring. -/
structure PVM (R : Type*) [Ring R] [StarRing R] where
  effect : Fin 5 → R
  selfadjoint : ∀ a, star (effect a) = effect a
  mul_eq : ∀ a b, effect a * effect b = if a = b then effect a else 0
  sum_one : ∑ a, effect a = 1

namespace PVM
variable {R : Type*} [Ring R] [StarRing R]

@[simp] theorem mul_self (P : PVM R) (a : Fin 5) : P.effect a * P.effect a = P.effect a := by
  simp [P.mul_eq]

theorem mul_of_ne (P : PVM R) {a b : Fin 5} (h : a ≠ b) :
    P.effect a * P.effect b = 0 := by simp [P.mul_eq, h]

end PVM


end CGLMP5
