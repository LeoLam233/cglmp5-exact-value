import CGLMP5.WordSyntax
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Star.Unitary

/-!
# Ordered noncommutative words for the CGLMP5 certificate

A party word retains the order of its two generators. Only adjacent powers of
one generator are combined. The two party lists are separated, and only the
explicit cross-party commutation hypothesis is used in their interpretation.
-/
namespace CGLMP5

namespace PartyWord

def eval {M : Type*} [Monoid M] (g : Fin 2 → M) (w : PartyWord) : M :=
  (w.map fun a => g a.1 ^ a.2).prod

@[simp] theorem eval_nil {M : Type*} [Monoid M] (g : Fin 2 → M) :
    eval g [] = 1 := rfl

@[simp] theorem eval_cons {M : Type*} [Monoid M] (g : Fin 2 → M)
    (a : Letter) (w : PartyWord) :
    eval g (a :: w) = g a.1 ^ a.2 * eval g w := rfl

@[simp] theorem eval_append {M : Type*} [Monoid M] (g : Fin 2 → M)
    (v w : PartyWord) : eval g (v ++ w) = eval g v * eval g w := by
  simp only [eval, List.map_append, List.prod_append]

theorem eval_push {M : Type*} [Monoid M] (g : Fin 2 → M)
    (hfive : ∀ i, g i ^ 5 = 1) (a : Letter) (w : PartyWord) :
    eval g (push a w) = g a.1 ^ a.2 * eval g w := by
  rcases a with ⟨i, n⟩
  have hn : g i ^ n = g i ^ (n % 5) := pow_eq_pow_mod n (hfive i)
  by_cases hz : n % 5 = 0
  · simp [push, hz, hn]
  · cases w with
    | nil => simp [push, hz, hn]
    | cons b t =>
      rcases b with ⟨j, m⟩
      by_cases hij : i = j
      · subst j
        have hm : g i ^ ((n % 5 + m) % 5) = g i ^ n * g i ^ m := by
          rw [← pow_eq_pow_mod (n % 5 + m) (hfive i), pow_add, ← hn]
        by_cases hmz : (n % 5 + m) % 5 = 0
        · have hp : g i ^ n * g i ^ m = 1 := by rw [← hm, hmz, pow_zero]
          simp [push, hz, hmz, ← mul_assoc, hp]
        · simp only [push, Prod.fst, Prod.snd, hz, ↓reduceIte, hmz, eval_cons]
          rw [hm, mul_assoc]
      · simp [push, hz, hij, hn]

/-- Every reduction is sound in every order-five monoid representation. -/
theorem eval_reduce {M : Type*} [Monoid M] (g : Fin 2 → M)
    (hfive : ∀ i, g i ^ 5 = 1) (w : PartyWord) :
    eval g (reduce w) = eval g w := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [reduce, eval_push g hfive, ih, eval_cons]

theorem pow_inverse_mod_five {G : Type*} [Group G] (a : G)
    (hfive : a ^ 5 = 1) (n : ℕ) : a ^ (5 - n % 5) = (a ^ n)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [pow_eq_pow_mod n hfive, ← pow_add,
    Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt n (by decide))), hfive]

theorem eval_adjoint {G : Type*} [Group G] (g : Fin 2 → G)
    (hfive : ∀ i, g i ^ 5 = 1) (w : PartyWord) :
    eval g (adjoint w) = (eval g w)⁻¹ := by
  rw [adjoint, eval_reduce g hfive]
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.reverse_cons, List.map_append, List.map_singleton,
      eval_append, eval_cons, eval_nil, mul_one, mul_inv_rev]
    rw [ih, pow_inverse_mod_five _ (hfive a.1)]

theorem eval_commute {M : Type*} [Monoid M] (a b : Fin 2 → M)
    (hab : ∀ i j, Commute (a i) (b j)) (v w : PartyWord) :
    Commute (eval a v) (eval b w) := by
  have hsingle (x : Letter) : Commute (a x.1 ^ x.2) (eval b w) := by
    induction w with
    | nil => simp
    | cons y w ihw =>
      rw [eval_cons]
      exact Commute.mul_right ((hab x.1 y.1).pow_pow x.2 y.2) ihw
  induction v with
  | nil => simp
  | cons x v ih =>
    rw [eval_cons]
    exact Commute.mul_left (hsingle x) ih

end PartyWord

namespace Word

def eval {M : Type*} [Monoid M] (a b : Fin 2 → M) (w : Word) : M :=
  PartyWord.eval a w.alice * PartyWord.eval b w.bob

@[simp] theorem eval_one {M : Type*} [Monoid M] (a b : Fin 2 → M) :
    eval a b one = 1 := by simp [eval, one]

theorem eval_mul {M : Type*} [Monoid M] (a b : Fin 2 → M)
    (ha : ∀ i, a i ^ 5 = 1) (hb : ∀ i, b i ^ 5 = 1)
    (hab : ∀ i j, Commute (a i) (b j)) (v w : Word) :
    eval a b (mul v w) = eval a b v * eval a b w := by
  simp only [eval, mul, PartyWord.eval_reduce a ha, PartyWord.eval_reduce b hb,
    PartyWord.eval_append]
  have hc := PartyWord.eval_commute a b hab w.alice v.bob
  calc
    _ = PartyWord.eval a v.alice *
        (PartyWord.eval a w.alice * PartyWord.eval b v.bob) * PartyWord.eval b w.bob := by
          simp only [mul_assoc]
    _ = _ := by rw [hc.eq]; simp only [mul_assoc]

theorem eval_adjoint {G : Type*} [Group G] (a b : Fin 2 → G)
    (ha : ∀ i, a i ^ 5 = 1) (hb : ∀ i, b i ^ 5 = 1)
    (hab : ∀ i j, Commute (a i) (b j)) (w : Word) :
    eval a b (adjoint w) = (eval a b w)⁻¹ := by
  simp only [eval, adjoint, PartyWord.eval_adjoint a ha, PartyWord.eval_adjoint b hb,
    mul_inv_rev]
  exact ((PartyWord.eval_commute a b hab w.alice w.bob).inv_left.inv_right).eq

/-- Evaluation in a star-monoid needs inverses only for unitary generators. -/
def evalStar {R : Type*} [Monoid R] [StarMul R]
    (a b : Fin 2 → unitary R) (w : Word) : R := (eval a b w : unitary R)

theorem evalStar_mul {R : Type*} [Monoid R] [StarMul R]
    (a b : Fin 2 → unitary R)
    (ha : ∀ i, a i ^ 5 = 1) (hb : ∀ i, b i ^ 5 = 1)
    (hab : ∀ i j, Commute (a i) (b j)) (v w : Word) :
    evalStar a b (mul v w) = evalStar a b v * evalStar a b w := by
  exact congrArg Subtype.val (eval_mul a b ha hb hab v w)

theorem evalStar_adjoint {R : Type*} [Monoid R] [StarMul R]
    (a b : Fin 2 → unitary R)
    (ha : ∀ i, a i ^ 5 = 1) (hb : ∀ i, b i ^ 5 = 1)
    (hab : ∀ i j, Commute (a i) (b j)) (w : Word) :
    evalStar a b (adjoint w) = star (evalStar a b w) := by
  exact congrArg Subtype.val (eval_adjoint a b ha hb hab w)

end Word
end CGLMP5
