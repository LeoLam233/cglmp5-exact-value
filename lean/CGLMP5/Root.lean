import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The actual algebraic embedding of the CGLMP5 certificate

The definition of `mu` is analytic, and selects the largest real root of the
literal published sextic. No finite arithmetic checker or external numerical
root calculation is a premise of this module.
-/

namespace CGLMP5

noncomputable section

/-- The exact sextic printed in the v0.1.1 theorem. -/
def sextic (t : ℝ) : ℝ := 5 * t ^ 6 - 65 * t ^ 4 + 144 * t ^ 2 + 96 * t + 16

lemma sextic_three : sextic 3 = -20 := by norm_num [sextic]
lemma sextic_31_div_10_pos : 0 < sextic (31 / 10) := by norm_num [sextic]

lemma sextic_shift (h : ℝ) : sextic (3 + h) =
    5*h^6 + 90*h^5 + 610*h^4 + 1920*h^3 + 2709*h^2 + 1230*h - 20 := by
  unfold sextic
  ring

/-- Above three all nonconstant coefficients of the shifted polynomial are positive. -/
lemma sextic_strictMonoOn : StrictMonoOn sextic (Set.Ici 3) := by
  intro a ha b hb hab
  have ha0 : 0 ≤ a - 3 := sub_nonneg.mpr ha
  have hab' : a - 3 ≤ b - 3 := by linarith
  have h2 := pow_le_pow_left₀ ha0 hab' 2
  have h3 := pow_le_pow_left₀ ha0 hab' 3
  have h4 := pow_le_pow_left₀ ha0 hab' 4
  have h5 := pow_le_pow_left₀ ha0 hab' 5
  have h6 := pow_le_pow_left₀ ha0 hab' 6
  have ea : a = 3 + (a - 3) := by ring
  have eb : b = 3 + (b - 3) := by ring
  rw [ea, eb, sextic_shift, sextic_shift]
  nlinarith

lemma exists_mu : ∃ t : ℝ, 3 < t ∧ t < 31 / 10 ∧ sextic t = 0 := by
  have hc : Continuous sextic := by unfold sextic; fun_prop
  have h := intermediate_value_Icc (show (3:ℝ) ≤ 31/10 by norm_num) hc.continuousOn
  have hz : (0:ℝ) ∈ Set.Icc (sextic 3) (sextic (31/10)) :=
    ⟨by rw [sextic_three]; norm_num, le_of_lt sextic_31_div_10_pos⟩
  obtain ⟨t, ht, hp⟩ := h hz
  refine ⟨t, ?_, ?_, hp⟩
  · have hne : t ≠ 3 := by intro he; subst t; norm_num [sextic] at hp
    exact lt_of_le_of_ne ht.1 (Ne.symm hne)
  · have hne : t ≠ 31/10 := by intro he; subst t; exact (ne_of_gt sextic_31_div_10_pos) hp
    exact lt_of_le_of_ne ht.2 hne

/-- The unique real root above three, proved below to be the largest real root. -/
def mu : ℝ := Classical.choose exists_mu
lemma mu_gt_three : 3 < mu := (Classical.choose_spec exists_mu).1
lemma mu_lt_31_div_10 : mu < 31/10 := (Classical.choose_spec exists_mu).2.1
lemma sextic_mu : sextic mu = 0 := (Classical.choose_spec exists_mu).2.2
lemma mu_pos : 0 < mu := lt_trans (by norm_num) mu_gt_three

lemma mu_largest_root (t : ℝ) (ht : sextic t = 0) : t ≤ mu := by
  by_contra hn
  have hmt : mu < t := lt_of_not_ge hn
  have h := sextic_strictMonoOn (le_of_lt mu_gt_three) (le_trans (le_of_lt mu_gt_three) (le_of_lt hmt)) hmt
  rw [ht, sextic_mu] at h
  exact lt_irrefl _ h

lemma mu_unique_above_three (t : ℝ) (h3 : 3 ≤ t) (hp : sextic t = 0) : t = mu := by
  apply le_antisymm (mu_largest_root t hp)
  by_contra hn
  have htm : t < mu := lt_of_not_ge hn
  have h := sextic_strictMonoOn h3 (le_of_lt mu_gt_three) htm
  rw [hp, sextic_mu] at h
  exact lt_irrefl _ h

/-- The positive square root, fixing the real embedding. -/
def s : ℝ := Real.sqrt 5
/-- The second positive square root, fixing the real embedding. -/
def u : ℝ := Real.sqrt (10 + 2*s)
def x : ℝ := 5*mu

lemma s_pos : 0 < s := Real.sqrt_pos.2 (by norm_num)
lemma s_sq : s^2 = 5 := Real.sq_sqrt (by norm_num)
lemma s_gt_two : 2 < s := by nlinarith [s_sq, s_pos]
lemma s_lt_three : s < 3 := by nlinarith [s_sq, s_pos]
lemma u_pos : 0 < u := Real.sqrt_pos.2 (by linarith [s_pos])
lemma u_sq : u^2 = 10 + 2*s := Real.sq_sqrt (by linarith [s_pos])
lemma u_gt_three : 3 < u := by nlinarith [u_sq, u_pos, s_pos]
lemma u_lt_four : u < 4 := by nlinarith [u_sq, u_pos, s_lt_three]

lemma mu_cubic : mu^3 = s*mu^2 + (4 - 4*s/5)*mu + 4 - 8*s/5 := by
  have hm : 0 < mu - 3 := sub_pos.mpr mu_gt_three
  have hmp : 0 < mu := mu_pos
  let A : ℝ := 5*(mu^3 - 4*mu - 4)
  let B : ℝ := 5*mu^2 - 4*mu - 8
  have hA : 0 < A := by
    have he : A = 5*((mu-3)*(mu^2+3*mu+5)+11) := by dsimp [A]; ring
    rw [he]
    positivity
  have hB : 0 < B := by
    have he : B = (mu-3)*(5*mu+11)+25 := by dsimp [B]; ring
    rw [he]
    positivity
  have hrel : A^2 - 5*B^2 = 0 := by
    calc
      A^2 - 5*B^2 = 5*sextic mu := by dsimp [A, B, sextic]; ring
      _ = 0 := by rw [sextic_mu]; ring
  have hsq : A^2 = (s*B)^2 := by nlinarith [s_sq]
  have hsb : 0 < s*B := mul_pos s_pos hB
  have heq : A = s*B := by nlinarith
  dsimp [A, B] at heq
  nlinarith [heq]

lemma x_cubic : x^3 = 5*s*x^2 + (100-20*s)*x + 500-200*s := by
  dsimp [x]
  nlinarith [mu_cubic]

/-- The actual twentieth root used by the published Fourier strategy. -/
def zeta : ℂ := ((u : ℂ) + Complex.I*((s : ℂ)-1))/4

lemma sin_pi_div_ten : Real.sin (Real.pi/10) = (s-1)/4 := by
  have he : Real.pi/10 = Real.pi/2 - 2*(Real.pi/5) := by ring
  rw [he, Real.sin_pi_div_two_sub, Real.cos_two_mul, Real.cos_pi_div_five]
  change 2*((1+s)/4)^2-1 = (s-1)/4
  nlinarith [s_sq]

lemma cos_pi_div_ten : Real.cos (Real.pi/10) = u/4 := by
  have hp : 0 < Real.cos (Real.pi/10) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have h := Real.sin_sq_add_cos_sq (Real.pi/10)
  rw [sin_pi_div_ten] at h
  nlinarith [s_sq, u_sq, u_pos]

/-- The algebraic root is the physical positive-angle Fourier branch. -/
lemma zeta_eq_exp : zeta = Complex.exp (((Real.pi/10 : ℝ) : ℂ)*Complex.I) := by
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, sin_pi_div_ten, cos_pi_div_ten]
  unfold zeta
  push_cast
  ring

lemma zeta_primitive : IsPrimitiveRoot zeta 20 := by
  rw [zeta_eq_exp]
  convert Complex.isPrimitiveRoot_exp 20 (by norm_num) using 1 <;> push_cast <;> congr 1 <;> ring

end
end CGLMP5
