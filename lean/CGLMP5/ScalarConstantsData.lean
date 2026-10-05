import CGLMP5.ScalarProductsBase
import CGLMP5.ScalarPowerData

namespace CGLMP5.Scalar

lemma eval_zeta : eval zetaExact = zeta := by
  norm_num [eval, zetaExact, ofCanonical, basisEval, Fin.sum_univ_succ, zeta]
  ring

lemma eval_mu : eval muExact = (mu : ℂ) := by
  norm_num [eval, muExact, ofCanonical, basisEval, Fin.sum_univ_succ, x]
  ring

lemma eval_pow_of_table_sound
    (hTable : ∀ i j : Fin 24,
      (∑ k : Fin 24, (mulCoeff i j k : ℂ)*basisEval k) = basisEval i*basisEval j)
    (a : Scalar) (n : ℕ) : eval (pow a n) = (eval a)^n := by
  induction n with
  | zero => simp [pow]
  | succ n hn => rw [pow, eval_mul_of_table_sound hTable, hn, pow_succ]

end CGLMP5.Scalar
