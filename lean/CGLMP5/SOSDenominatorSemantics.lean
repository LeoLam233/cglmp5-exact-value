import CGLMP5.ScalarIntegerArithmetic
import Mathlib.Tactic.Ring

/-! # Denominator-cleared exact arithmetic semantics

These identities replace repeated rational normalization by kernel-visible integer convolution
and a single division. They do not change any scalar interpretation.
-/

namespace CGLMP5.Scalar

/-- Exact numerator/denominator factorization of scalar multiplication. Zero denominators are
  handled by the field's total division convention; canonical inputs separately prove positivity. -/
theorem mul_ofCanonical (n m : Fin 24 → ℤ) (d e : ℕ) (k : Fin 24) :
    mul (ofCanonical n d) (ofCanonical m e) k =
      (mulNumerator n m k : ℚ) / (d * e : ℕ) := by
  have h (xs : List (Fin 24 × Fin 24 × ℤ)) :
      (xs.map fun t => ((n t.1 : ℚ) / d) * ((m t.2.1 : ℚ) / e) * (t.2.2 : ℚ)).sum =
        (((xs.map fun t => n t.1 * m t.2.1 * t.2.2).sum : ℤ) : ℚ) / ((d : ℚ) * (e : ℚ)) := by
    induction xs with
    | nil => simp
    | cons t xs ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul, ih]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  simpa only [mul, ofCanonical, mulNumerator, Nat.cast_mul] using h (mulTerms k)

end CGLMP5.Scalar

namespace CGLMP5.SOSFinite

/-- Rescale one exact rational to a certified common positive denominator. -/
theorem common_denominator_term (N : ℤ) (D L : ℕ) (hD : 0 < D) (hL : 0 < L)
    (hdiv : L % D = 0) :
    (N : ℚ) / D = (((L / D : ℕ) : ℤ) * N : ℤ) / (L : ℚ) := by
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hL' : (L : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hm : ((L / D : ℕ) : ℚ) * (D : ℚ) = (L : ℚ) := by
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
  apply (div_eq_div_iff hD' hL').mpr
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [← hm]
  ring

/-- A finite list of exact rational terms can be checked with one integer numerator sum. -/
theorem list_common_denominator (terms : List (ℤ × ℕ)) (L : ℕ) (hL : 0 < L)
    (hpositive : ∀ t ∈ terms, 0 < t.2) (hdiv : ∀ t ∈ terms, L % t.2 = 0) :
    (terms.map fun t => (t.1 : ℚ) / t.2).sum =
      (((terms.map fun t => ((L / t.2 : ℕ) : ℤ) * t.1).sum : ℤ) : ℚ) / L := by
  induction terms with
  | nil => simp
  | cons t terms ih =>
    have hp := hpositive t (by simp)
    have hd := hdiv t (by simp)
    have hpt : ∀ u ∈ terms, 0 < u.2 := fun u hu => hpositive u (by simp [hu])
    have hdt : ∀ u ∈ terms, L % u.2 = 0 := fun u hu => hdiv u (by simp [hu])
    simp only [List.map_cons, List.sum_cons, Int.cast_add]
    rw [common_denominator_term t.1 t.2 L hp hL hd, ih hpt hdt]
    exact (add_div _ _ _).symm


/-- A denominator-cleared integer equality certifies the original exact rational equality. -/
theorem list_common_denominator_eq (terms : List (ℤ × ℕ))
    (L : ℕ) (N : ℤ) (D : ℕ) (hL : 0 < L) (hD : 0 < D)
    (hpositive : ∀ t ∈ terms, 0 < t.2) (hdiv : ∀ t ∈ terms, L % t.2 = 0)
    (hTargetDiv : L % D = 0)
    (hInteger : (terms.map fun t => ((L / t.2 : ℕ) : ℤ) * t.1).sum =
      ((L / D : ℕ) : ℤ) * N) :
    (terms.map fun t => (t.1 : ℚ) / t.2).sum = (N : ℚ) / D := by
  rw [list_common_denominator terms L hL hpositive hdiv, hInteger]
  exact (common_denominator_term N D L hD hL hTargetDiv).symm

end CGLMP5.SOSFinite
