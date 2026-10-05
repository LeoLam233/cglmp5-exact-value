import CGLMP5.Measurements
import Mathlib.Algebra.Star.Unitary

namespace CGLMP5

variable {R : Type*} [Ring R] [StarRing R]

/-- Unitary conjugation preserves every defining PVM relation. -/
def PVM.unitaryConjugate (P : PVM R) (U : unitary R) : PVM R where
  effect a := star (U : R) * P.effect a * U
  selfadjoint a := by simp [star_mul, P.selfadjoint, mul_assoc]
  mul_eq a b := by
    calc
      (star (U : R) * P.effect a * U) * (star (U : R) * P.effect b * U) =
        star (U : R) * (P.effect a * ((U : R) * star (U : R)) * P.effect b) * U := by
          simp only [mul_assoc]
      _ = star (U : R) * (P.effect a * P.effect b) * U := by
        rw [Unitary.mul_star_self_of_mem U.property, mul_one]
      _ = if a = b then star (U : R) * P.effect a * U else 0 := by
        rw [P.mul_eq]
        split_ifs <;> simp [mul_assoc]
  sum_one := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, P.sum_one, mul_one]
    exact Unitary.star_mul_self_of_mem U.property

@[simp] theorem PVM.unitaryConjugate_effect (P : PVM R) (U : unitary R) (a : Fin 5) :
    (P.unitaryConjugate U).effect a = star (U : R) * P.effect a * U := rfl

end CGLMP5
