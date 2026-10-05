import CGLMP5.ScalarDefs

namespace CGLMP5.Scalar

lemma canonical_denominator_nonzero (d : ℕ) (hd : 0 < d) : (d : ℂ) ≠ 0 := by
  exact_mod_cast Nat.ne_of_gt hd

lemma eval_ofCanonical (n : Fin 24 → ℤ) (d : ℕ) :
    eval (ofCanonical n d) = (∑ k : Fin 24, (n k : ℂ)*basisEval k)/(d : ℂ) := by
  simp only [eval, ofCanonical]
  push_cast
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring


end CGLMP5.Scalar
