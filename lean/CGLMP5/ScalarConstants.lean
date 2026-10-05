import CGLMP5.Scalar
import CGLMP5.ScalarConstantsData

namespace CGLMP5.Scalar

lemma eval_pow (a : Scalar) (n : ℕ) : eval (pow a n) = (eval a)^n :=
  eval_pow_of_table_sound mulCoeff_sound a n

end CGLMP5.Scalar
