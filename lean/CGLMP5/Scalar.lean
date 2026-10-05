import CGLMP5.ScalarTable
import CGLMP5.ScalarEncoding

/-! Sound evaluation of the finite exact scalar arithmetic in the actual embedding. -/

namespace CGLMP5.Scalar

lemma eval_mul (a b : Scalar) : eval (mul a b) = eval a * eval b :=
  eval_mul_of_table_sound mulCoeff_sound a b


end CGLMP5.Scalar
