import Mathlib.Algebra.Star.BigOperators
import CGLMP5.Measurements
import Mathlib.Algebra.Star.Unitary
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace CGLMP5.PVM

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

/-- A permutation changes outcome labels without changing projectivity/completeness. -/
def reindex (P : PVM R) (e : Fin 5 ≃ Fin 5) : PVM R where
  effect a := P.effect (e a)
  selfadjoint a := P.selfadjoint (e a)
  mul_eq a b := by simpa only [Equiv.apply_eq_iff_eq] using P.mul_eq (e a) (e b)
  sum_one := (e.sum_comp P.effect).trans P.sum_one

/-- Finite spectral calculus for one projective measurement. -/
noncomputable def eval (P : PVM R) (f : Fin 5 → ℂ) : R := ∑ a, f a • P.effect a

@[simp] theorem eval_one (P : PVM R) : P.eval (fun _ => 1) = 1 := by
  simp [eval, P.sum_one]

theorem eval_mul (P : PVM R) (f g : Fin 5 → ℂ) :
    P.eval f * P.eval g = P.eval (fun a => f a * g a) := by
  simp [eval, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    smul_smul, P.mul_eq, smul_ite, Finset.sum_ite_eq', Finset.mem_univ, mul_comm]

/-- Bilinear spectral expansion preserves the given operator order. -/
theorem eval_mul_eval (P Q : PVM R) (f g : Fin 5 → ℂ) :
    P.eval f * Q.eval g = ∑ a, ∑ b, (f a*g b) • (P.effect a * Q.effect b) := by
  unfold eval
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

theorem eval_pow (P : PVM R) (f : Fin 5 → ℂ) (n : Nat) :
    (P.eval f)^n = P.eval (fun a => (f a)^n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, eval_mul]; simp only [pow_succ]

theorem star_eval (P : PVM R) (f : Fin 5 → ℂ) :
    star (P.eval f) = P.eval (fun a => star (f a)) := by
  simp [eval, star_sum, star_smul, P.selfadjoint]

noncomputable def phase (P : PVM R) (ω : ℂ) : R := P.eval (fun a => ω^a.val)

theorem phase_fifth (P : PVM R) (ω : ℂ) (hω : ω^5=1) : (P.phase ω)^5=1 := by
  rw [phase, eval_pow]
  have h : (fun a : Fin 5 => (ω^a.val)^5) = fun _ => (1:ℂ) := by
    funext a
    rw [← pow_mul, Nat.mul_comm, pow_mul, hω, one_pow]
  rw [h, eval_one]

theorem phase_mem_unitary (P : PVM R) (ω : ℂ) (hω : star ω * ω = 1) :
    P.phase ω ∈ unitary R := by
  rw [Unitary.mem_iff]
  have hf : (fun a : Fin 5 => star (ω^a.val) * ω^a.val) = fun _ => (1:ℂ) := by
    funext a
    rw [star_pow, ← mul_pow, hω, one_pow]
  constructor
  · rw [phase, star_eval, eval_mul, hf, eval_one]
  · rw [phase, star_eval, eval_mul]
    have h : (fun a : Fin 5 => ω^a.val * star (ω^a.val)) = fun _ => (1:ℂ) := by
      simpa only [mul_comm] using hf
    rw [h, eval_one]

noncomputable def phaseUnitary (P : PVM R) (ω : ℂ) (hω : star ω * ω = 1) : unitary R :=
  ⟨P.phase ω, P.phase_mem_unitary ω hω⟩

/-- Only cross-party effect commutation is needed for the spectral unitaries. -/
theorem phase_commute (P Q : PVM R) (ω : ℂ)
    (h : ∀ a b, Commute (P.effect a) (Q.effect b)) :
    Commute (P.phase ω) (Q.phase ω) := by
  unfold phase eval
  apply Commute.sum_left
  intro a _
  apply Commute.sum_right
  intro b _
  exact ((h a b).smul_left _).smul_right _

end CGLMP5.PVM
