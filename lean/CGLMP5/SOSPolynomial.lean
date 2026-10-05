import CGLMP5.SOSDefinitions
import Mathlib.Algebra.Star.Module

/-! Sound finite noncommutative polynomial operations in arbitrary complex star-algebras. -/
namespace CGLMP5.SOS
noncomputable section

abbrev Polynomial := List (Word × ℂ)

def polyScale (c : ℂ) (p : Polynomial) : Polynomial := p.map fun t => (t.1, c * t.2)
def polyMul (p q : Polynomial) : Polynomial :=
  p.flatMap fun t => q.map fun u => (Word.mul t.1 u.1, t.2 * u.2)
def polyAdjoint (p : Polynomial) : Polynomial := p.map fun t => (Word.adjoint t.1, star t.2)

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  (a b : Fin 2 → unitary R)
  (ha : ∀ i, a i ^ 5 = 1) (hb : ∀ i, b i ^ 5 = 1)
  (hab : ∀ i j, Commute (a i) (b j))

@[simp] theorem evaluate_nil : evaluate a b [] = 0 := rfl
@[simp] theorem evaluate_cons (t : Word × ℂ) (p : Polynomial) :
    evaluate a b (t :: p) = t.2 • Word.evalStar a b t.1 + evaluate a b p := rfl
@[simp] theorem evaluate_append (p q : Polynomial) :
    evaluate a b (p ++ q) = evaluate a b p + evaluate a b q := by
  simp [evaluate, List.map_append, List.sum_append]

theorem evaluate_scale (c : ℂ) (p : Polynomial) :
    evaluate a b (polyScale c p) = c • evaluate a b p := by
  induction p with
  | nil => simp [polyScale]
  | cons t p ih =>
    simp only [polyScale] at ih ⊢
    simp [ih, smul_add, mul_smul]

include ha hb hab in
include ha hb hab in
theorem evaluate_mul_single (t : Word × ℂ) (q : Polynomial) :
    evaluate a b (q.map fun u => (Word.mul t.1 u.1, t.2 * u.2)) =
      (t.2 • Word.evalStar a b t.1) * evaluate a b q := by
  induction q with
  | nil => simp
  | cons u q ih =>
    simp only [List.map_cons, evaluate_cons, Word.evalStar_mul a b ha hb hab, ih, mul_add]
    congr 1
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]

include ha hb hab in
theorem evaluate_mul (p q : Polynomial) :
    evaluate a b (polyMul p q) = evaluate a b p * evaluate a b q := by
  induction p with
  | nil => simp [polyMul]
  | cons t p ih =>
    simp only [polyMul] at ih
    simp only [polyMul, List.flatMap_cons, evaluate_append, evaluate_cons, add_mul]
    rw [evaluate_mul_single a b ha hb hab, ih]

include ha hb hab in
theorem evaluate_adjoint [StarModule ℂ R] (p : Polynomial) :
    evaluate a b (polyAdjoint p) = star (evaluate a b p) := by
  induction p with
  | nil => simp [polyAdjoint]
  | cons t p ih =>
    simp only [polyAdjoint] at ih ⊢
    simp only [List.map_cons, evaluate_cons, Word.evalStar_adjoint a b ha hb hab,
      star_add, star_smul, ih]

def polyAnticommutator (c : ℂ) (p : Polynomial) : Polynomial :=
  polyScale c (polyMul (polyAdjoint p) p ++ polyMul p (polyAdjoint p))

include ha hb hab in
theorem evaluate_anticommutator [StarModule ℂ R] (c : ℂ) (p : Polynomial) :
    evaluate a b (polyAnticommutator c p) =
      c • (star (evaluate a b p) * evaluate a b p +
        evaluate a b p * star (evaluate a b p)) := by
  rw [polyAnticommutator, evaluate_scale, evaluate_append,
    evaluate_mul a b ha hb hab, evaluate_mul a b ha hb hab,
    evaluate_adjoint a b ha hb hab]

/-- Coefficient extraction retains the complete ordered word. -/
def coefficient (p : Polynomial) (w : Word) : ℂ :=
  ((p.filter fun t => t.1 = w).map Prod.snd).sum

@[simp] theorem coefficient_nil (w : Word) : coefficient [] w = 0 := rfl
@[simp] theorem coefficient_cons (t : Word × ℂ) (p : Polynomial) (w : Word) :
    coefficient (t :: p) w = (if t.1 = w then t.2 else 0) + coefficient p w := by
  by_cases h : t.1 = w <;> simp [coefficient, h]

/-- Collecting coefficients over a finite containing support preserves evaluation. -/
theorem evaluate_eq_sum_coefficients (p : Polynomial) (support : Finset Word)
    (hmem : ∀ t ∈ p, t.1 ∈ support) :
    evaluate a b p = ∑ w ∈ support, coefficient p w • Word.evalStar a b w := by
  induction p with
  | nil => simp
  | cons t p ih =>
    have ht : t.1 ∈ support := hmem t (by simp)
    have hp : ∀ u ∈ p, u.1 ∈ support := fun u hu => hmem u (by simp [hu])
    rw [evaluate_cons, ih hp]
    simp only [coefficient_cons, add_smul, Finset.sum_add_distrib]
    congr 1
    simp [ht, eq_comm]

/-- Equality of all ordered coefficients implies equality in every allowed representation. -/
theorem evaluate_eq_of_coefficients (p q : Polynomial) (support : Finset Word)
    (hp : ∀ t ∈ p, t.1 ∈ support) (hq : ∀ t ∈ q, t.1 ∈ support)
    (hc : ∀ w ∈ support, coefficient p w = coefficient q w) :
    evaluate a b p = evaluate a b q := by
  rw [evaluate_eq_sum_coefficients a b p support hp,
    evaluate_eq_sum_coefficients a b q support hq]
  apply Finset.sum_congr rfl
  intro w hw
  rw [hc w hw]

end
end CGLMP5.SOS
