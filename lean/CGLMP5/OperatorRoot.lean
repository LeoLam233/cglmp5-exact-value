import CGLMP5.Root
import Mathlib.Algebra.BigOperators.Fin

namespace CGLMP5

/-- The exact phase used by the certificate is a primitive fifth root. -/
lemma zeta_four_primitive : IsPrimitiveRoot (zeta^4) 5 := by
  simpa using zeta_primitive.pow_div_gcd 4 (by decide)

lemma zeta_four_fifth : (zeta^4)^5 = 1 := zeta_four_primitive.pow_eq_one

lemma zeta_four_unitary : star (zeta^4) * zeta^4 = 1 := by
  have hn := zeta_four_primitive.norm'_eq_one (by decide)
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hn]
  norm_num

lemma zeta_four_sum : 1 + zeta^4 + (zeta^4)^2 + (zeta^4)^3 + (zeta^4)^4 = 0 := by
  have h := zeta_four_primitive.geom_sum_eq_zero (by decide)
  simpa [Finset.sum_range_succ] using h

end CGLMP5
