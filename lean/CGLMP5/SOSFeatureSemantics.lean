import CGLMP5.SOSPolynomial
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin

/-! # Sound coefficient fibers for optimized exact feature tables -/

namespace CGLMP5.SOS
noncomputable section

/-- All features attached to the same complete ordered word. -/
def featureFiber {Feature : Type*} (entries : List (Word × Feature)) (w : Word) : List Feature :=
  (entries.filter fun e => e.1 = w).map Prod.snd

/-- Interpret a feature table with its actual complex scalar value function. -/
def featurePolynomial {Feature : Type*} (value : Feature → ℂ)
    (entries : List (Word × Feature)) : Polynomial :=
  entries.map fun e => (e.1, value e.2)

/-- Fiber sums are exactly the coefficients of the interpreted ordered-word polynomial. -/
theorem coefficient_featurePolynomial {Feature : Type*} (value : Feature → ℂ)
    (entries : List (Word × Feature)) (w : Word) :
    coefficient (featurePolynomial value entries) w =
      ((featureFiber entries w).map value).sum := by
  induction entries with
  | nil => rfl
  | cons e entries ih =>
    simp only [featurePolynomial, List.map_cons, coefficient_cons] at ih ⊢
    by_cases h : e.1 = w <;> simp [featureFiber, h, ih]

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  (a b : Fin 2 → unitary R)

/-- Exact finite fiber equalities imply equality in every bounded or abstract representation. -/
theorem evaluate_featurePolynomial_eq {Feature : Type*} (value : Feature → ℂ)
    (entries : List (Word × Feature)) (target : Polynomial) (support : Finset Word)
    (hentries : ∀ e ∈ entries, e.1 ∈ support)
    (htarget : ∀ t ∈ target, t.1 ∈ support)
    (hfiber : ∀ w ∈ support, ((featureFiber entries w).map value).sum = coefficient target w) :
    evaluate a b (featurePolynomial value entries) = evaluate a b target := by
  refine evaluate_eq_of_coefficients a b _ target support ?_ htarget ?_
  · intro t ht
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp ht
    exact hentries e he
  · intro w hw
    rw [coefficient_featurePolynomial]
    exact hfiber w hw

/-- Evaluation commutes with literal concatenation of arbitrary polynomial lists. -/
theorem evaluate_flatMap {ι : Type*} (p : ι → Polynomial) (indices : List ι) :
    evaluate a b (indices.flatMap p) = (indices.map fun j => evaluate a b (p j)).sum := by
  induction indices with
  | nil => rfl
  | cons j indices ih =>
    simp only [List.flatMap_cons, evaluate_append, List.map_cons, List.sum_cons, ih]

/-- In particular, concatenating the fourteen terms means their actual finite operator sum. -/
theorem evaluate_finRange_flatMap {n : ℕ} (p : Fin n → Polynomial) :
    evaluate a b ((List.finRange n).flatMap p) = ∑ j : Fin n, evaluate a b (p j) := by
  rw [evaluate_flatMap, ← List.ofFn_eq_map, List.sum_ofFn]

end
end CGLMP5.SOS
