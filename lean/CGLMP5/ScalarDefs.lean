import CGLMP5.Root
import CGLMP5.ScalarSyntax
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-! Actual complex interpretation of the exact scalar syntax. -/

namespace CGLMP5
namespace Scalar

noncomputable def basisEval (k : Fin 24) : ℂ :=
  (s : ℂ)^(k.val % 2) * (x : ℂ)^((k.val / 2) % 3) *
  (u : ℂ)^((k.val / 6) % 2) * Complex.I^(k.val / 12)

noncomputable def eval (a : Scalar) : ℂ := ∑ k : Fin 24, (a k : ℂ) * basisEval k
noncomputable def evalReal (a : Scalar) : ℝ := (eval a).re

@[simp] lemma eval_zero : eval zero = 0 := by simp [eval, zero]
@[simp] lemma eval_add (a b : Scalar) : eval (add a b) = eval a + eval b := by
  simp [eval, add, add_mul, Finset.sum_add_distrib]
@[simp] lemma eval_neg (a : Scalar) : eval (neg a) = -eval a := by simp [eval, neg]
@[simp] lemma eval_ofRat (q : ℚ) : eval (ofRat q) = (q : ℂ) := by
  unfold eval
  rw [Finset.sum_eq_single 0]
  · simp [ofRat, basisEval]
  · intro b _ hb
    simp [ofRat, hb]
  · simp

lemma basisEval_conj (k : Fin 24) :
    star (basisEval k) = if k.val < 12 then basisEval k else -basisEval k := by
  fin_cases k <;> norm_num [basisEval, map_mul, map_pow] <;> ring

@[simp] lemma eval_conj (a : Scalar) : eval (conj a) = star (eval a) := by
  simp only [eval, star_sum, star_mul, basisEval_conj]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : k.val < 12 <;> simp [conj, h, mul_comm]

lemma eval_eq_ofReal (a : Scalar) (ha : isReal a) : eval a = (evalReal a : ℂ) := by
  have hconj : conj a = a := by
    funext k
    by_cases hk : k.val < 12
    · simp [conj, hk]
    · have hz := ha k (by omega)
      simp [conj, hk, hz]
  have hs : star (eval a) = eval a := by rw [← eval_conj, hconj]
  apply Complex.ext
  · rfl
  · have hi := congrArg Complex.im hs
    simp only [Complex.star_def, Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

/-- The real tower monomial without the final power of `i`. -/
noncomputable def realMonomial (k : Fin 24) : ℝ :=
  s^(k.val % 2)*x^((k.val/2)%3)*u^((k.val/6)%2)

lemma basisEval_re (k : Fin 24) : (basisEval k).re =
    if k.val < 12 then realMonomial k else 0 := by
  fin_cases k <;> norm_num [basisEval, realMonomial, ← Complex.ofReal_pow]

lemma evalReal_eq (a : Scalar) : evalReal a =
    ∑ k : Fin 24, (a k : ℝ)*(if k.val < 12 then realMonomial k else 0) := by
  simp [evalReal, eval, Complex.mul_re, basisEval_re]

end Scalar
end CGLMP5
