import CGLMP5.ScalarTableData
import CGLMP5.ScalarDefs

namespace CGLMP5.Scalar

lemma weighted_list_sum (a b : Scalar) (l : List (Fin 24 × Fin 24 × ℤ)) :
    (l.map fun t => a t.1*b t.2.1*(t.2.2:ℚ)).sum =
      ∑ i : Fin 24, ∑ j : Fin 24, a i*b j*
        (((l.map fun t => if t.1=i ∧ t.2.1=j then t.2.2 else 0).sum : ℤ):ℚ) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, mul_add,
      Finset.sum_add_distrib]
    rw [ih]
    congr 1
    simp [ite_and, mul_ite, eq_comm]

lemma mul_eq_dense (a b : Scalar) (k : Fin 24) :
    mul a b k = ∑ i : Fin 24, ∑ j : Fin 24, a i*b j*(mulCoeff i j k : ℚ) :=
  weighted_list_sum a b (mulTerms k)

lemma sC_sq : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
lemma uC_sq : (u : ℂ)^2 = 10+2*(s : ℂ) := by exact_mod_cast u_sq
lemma xC_cubic : (x : ℂ)^3 = 5*(s : ℂ)*(x : ℂ)^2 +
    (100-20*(s : ℂ))*(x : ℂ) + 500-200*(s : ℂ) := by exact_mod_cast x_cubic

lemma eval_mul_of_table_sound
    (hTable : ∀ i j : Fin 24,
      (∑ k : Fin 24, (mulCoeff i j k : ℂ)*basisEval k) = basisEval i*basisEval j)
    (a b : Scalar) : eval (mul a b) = eval a * eval b := by
  unfold eval
  calc
    (∑ k : Fin 24, (mul a b k : ℂ) * basisEval k) =
        ∑ i : Fin 24, ∑ j : Fin 24,
          (a i : ℂ)*(b j : ℂ)*(∑ k : Fin 24, (mulCoeff i j k : ℂ)*basisEval k) := by
      simp only [mul_eq_dense]
      push_cast
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ i : Fin 24, ∑ j : Fin 24,
          (a i : ℂ)*(b j : ℂ)*(basisEval i*basisEval j) := by
      simp_rw [hTable]
    _ = (∑ i : Fin 24, (a i : ℂ)*basisEval i) *
        (∑ j : Fin 24, (b j : ℂ)*basisEval j) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring


end CGLMP5.Scalar
