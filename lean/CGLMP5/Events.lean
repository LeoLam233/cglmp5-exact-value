import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace CGLMP5

abbrev Outcome := Fin 5
abbrev Setting := Fin 2

/-- A literal modular event, `a = b + shift (mod 5)`. -/
def shifted (a b : Outcome) (shift : Nat) : Bool :=
  a.val == (b.val + shift) % 5

/-- Twice the contribution at one value of k in the published eight-event convention.
The arguments are A0,A1,B0,B1, in that order. -/
def deterministicTermTwo (a₀ a₁ b₀ b₁ : Outcome) (k : Fin 2) : Int :=
  (2 - (k.val : Int)) *
    ((if shifted a₀ b₀ k.val then 1 else 0) +
     (if shifted b₀ a₁ (k.val + 1) then 1 else 0) +
     (if shifted a₁ b₁ k.val then 1 else 0) +
     (if shifted b₁ a₀ k.val then 1 else 0) -
     (if shifted a₀ b₀ (4 - k.val) then 1 else 0) -
     (if shifted b₀ a₁ ((5 - k.val) % 5) then 1 else 0) -
     (if shifted a₁ b₁ (4 - k.val) then 1 else 0) -
     (if shifted b₁ a₀ (4 - k.val) then 1 else 0))

def deterministicTwo (a₀ a₁ b₀ b₁ : Outcome) : Int :=
  deterministicTermTwo a₀ a₁ b₀ b₁ 0 + deterministicTermTwo a₀ a₁ b₀ b₁ 1

/-- Kernel reduction checks all 625 deterministic local assignments, with no oracle. -/
theorem deterministicTwo_le_four :
    ∀ a₀ a₁ b₀ b₁ : Outcome, deterministicTwo a₀ a₁ b₀ b₁ ≤ 4 := by
  decide

theorem deterministicTwo_zero : deterministicTwo 0 0 0 0 = 4 := by decide

/-- The literal coefficient of P(a,b|x,y), scaled by two. -/
def eventCoefficientTwo (x y : Setting) (a b : Outcome) : Int :=
  ∑ k : Fin 2, (2 - (k.val : Int)) *
    if x.val == 0 then
      if y.val == 0 then
        (if shifted a b k.val then 1 else 0) -
        (if shifted a b (4-k.val) then 1 else 0)
      else
        (if shifted b a k.val then 1 else 0) -
        (if shifted b a (4-k.val) then 1 else 0)
    else
      if y.val == 0 then
        (if shifted b a (k.val+1) then 1 else 0) -
        (if shifted b a ((5-k.val)%5) then 1 else 0)
      else
        (if shifted a b k.val then 1 else 0) -
        (if shifted a b (4-k.val) then 1 else 0)

/-- The coefficient form agrees with the eight literal event families. -/
theorem coefficient_deterministic : ∀ a₀ a₁ b₀ b₁ : Outcome,
    eventCoefficientTwo 0 0 a₀ b₀ + eventCoefficientTwo 1 0 a₁ b₀ +
    eventCoefficientTwo 1 1 a₁ b₁ + eventCoefficientTwo 0 1 a₀ b₁ =
    deterministicTwo a₀ a₁ b₀ b₁ := by decide

/-- The oriented residue after the manuscript's D relabelling. -/
def eventResidue (x y : Setting) (a b : Outcome) : Nat :=
  if x.val == 0 then
    if y.val == 0 then (a.val + 5 - b.val) % 5 else (b.val + 5 - a.val) % 5
  else
    if y.val == 0 then (b.val + 9 - a.val) % 5 else (a.val + 5 - b.val) % 5

/-- Literal events and the cyclic f(z)=1-z/2 convention have identical coefficients. -/
theorem coefficient_cyclic : ∀ (x y : Setting) (a b : Outcome),
    eventCoefficientTwo x y a b = 2 - (eventResidue x y a b : Int) := by decide

/-- Standard five-outcome CGLMP functional, in local-bound-two normalization. -/
noncomputable def cglmp (P : Setting → Setting → Outcome → Outcome → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b, (eventCoefficientTwo x y a b : ℝ) / 2 * P x y a b

/-- The CGLMP functional is linear in the conditional probability table. -/
noncomputable def cglmpLinear :
    (Setting → Setting → Outcome → Outcome → ℝ) →ₗ[ℝ] ℝ where
  toFun := cglmp
  map_add' P Q := by simp [cglmp, mul_add, Finset.sum_add_distrib]
  map_smul' c P := by simp [cglmp, Finset.mul_sum, mul_assoc, mul_left_comm, mul_add]

abbrev Assignment := (Setting → Outcome) × (Setting → Outcome)

/-- A local deterministic behavior; no joint quantum measurement is posited. -/
def deterministicBehavior (σ : Assignment) (x y : Setting) (a b : Outcome) : ℝ :=
  if a = σ.1 x ∧ b = σ.2 y then 1 else 0

theorem cglmp_deterministic (σ : Assignment) :
    cglmp (deterministicBehavior σ) =
      (deterministicTwo (σ.1 0) (σ.1 1) (σ.2 0) (σ.2 1) : ℝ) / 2 := by
  simp only [cglmp, deterministicBehavior, ite_and, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero]
  simp only [Fin.sum_univ_two]
  have h := coefficient_deterministic (σ.1 0) (σ.1 1) (σ.2 0) (σ.2 1)
  have h' := congrArg (fun z : Int => (z : ℝ)) h
  push_cast at h'
  linarith

theorem cglmp_deterministic_le_two (σ : Assignment) :
    cglmp (deterministicBehavior σ) ≤ 2 := by
  rw [cglmp_deterministic]
  have h : (deterministicTwo (σ.1 0) (σ.1 1) (σ.2 0) (σ.2 1) : ℝ) ≤ 4 :=
    by exact_mod_cast deterministicTwo_le_four (σ.1 0) (σ.1 1) (σ.2 0) (σ.2 1)
  linarith

/-- Arbitrary local randomization is a convex mixture of the finite deterministic behaviors. -/
noncomputable def localBehavior (w : Assignment → ℝ) :
    Setting → Setting → Outcome → Outcome → ℝ :=
  ∑ σ, w σ • deterministicBehavior σ

theorem cglmp_local_bound (w : Assignment → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) (hunit : ∑ σ, w σ = 1) :
    cglmp (localBehavior w) ≤ 2 := by
  change cglmpLinear (∑ σ, w σ • deterministicBehavior σ) ≤ 2
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  calc
    _ ≤ ∑ σ, w σ * 2 := Finset.sum_le_sum fun σ _ =>
      mul_le_mul_of_nonneg_left (cglmp_deterministic_le_two σ) (hw σ)
    _ = 2 := by rw [← Finset.sum_mul, hunit, one_mul]

/-- The all-zero deterministic assignment attains the local bound. -/
theorem cglmp_zero_assignment :
    cglmp (deterministicBehavior (fun _ => 0, fun _ => 0)) = 2 := by
  rw [cglmp_deterministic, deterministicTwo_zero]
  norm_num

/-- Regression anchor for the asymmetric B0=A1+k+1 convention. -/
theorem asymmetric_event_anchor : eventCoefficientTwo 1 0 0 0 = -2 := by decide

end CGLMP5
