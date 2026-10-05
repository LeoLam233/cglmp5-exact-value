import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Exact Schmidt algebra for the full CGLMP5 attaining strategy.
The polynomial coefficients are the canonical SOS14.json gamma records,
rewritten with x=5m. Every displayed certificate is kernel-visible. -/
namespace CGLMP5.Attainment
noncomputable section

def f1 (s u : ℝ) : ℝ := u * (5 - s) / 20
def f2 (s : ℝ) : ℝ := (s - 1) / 2
def f3 (s u : ℝ) : ℝ := u * s / 10
def f4 (s : ℝ) : ℝ := (s + 1) / 2

def coeffA (m s u : ℝ) : ℝ :=
  u * (5 + s + 13*m + 6*s*m - 5*m^2 - 2*s*m^2) / 4

def coeffB (m s : ℝ) : ℝ :=
  (-18 - 8*s - 55*m - 24*s*m + 20*m^2 + 9*s*m^2) / 2

def schmidtDenom (m s u : ℝ) : ℝ := m * (m - f2 s) - 2 * (f1 s u)^2

def schmidtNumer (m s u : ℝ) : ℝ := m * (f1 s u + f3 s u) + 2 * f1 s u * f2 s

variable (m s u : ℝ)
variable (hs : s^2 = 5) (hu : u^2 = 10 + 2*s)
variable (hm : m^3 = s*m^2 + (4 - 4*s/5)*m + 4 - 8*s/5)
include hs hu hm

theorem f1_mul_u : f1 s u * u = 2 := by
  unfold f1
  linear_combination (1/4 - s/20) * hu + (-1/10) * hs

theorem two_s_mul_f3 : 2 * s * f3 s u = u := by
  unfold f3
  linear_combination (u/5) * hs

theorem f1_sq : (f1 s u)^2 = (5-s)/10 := by
  unfold f1
  linear_combination (s^2/400 - s/40 + 1/16) * hu + (s/200 - 1/40) * hs

theorem coeffA_mul_denom : coeffA m s u * schmidtDenom m s u = schmidtNumer m s u := by
  unfold coeffA schmidtDenom schmidtNumer f1 f2 f3
  linear_combination (-m*s*u/2 - 5*m*u/4 - s^2*u/4 + 5*s*u/8 + 21*u/8) * hm + (m^2*s^3*u/400 - 3*m^2*s^2*u/160 + 5*m^2*u/32 - 3*m*s^3*u/400 + 47*m*s^2*u/800 - m*s*u/40 - 13*m*u/32 - s^3*u/800 + s^2*u/160 + s*u/32 - 5*u/32) * hu + (m^2*s^2*u/200 - 21*m^2*s*u/80 + 9*m^2*u/80 - 3*m*s^2*u/200 + 97*m*s*u/400 - 29*m*u/80 - s^2*u/400 + 2*s*u/5 - 147*u/80) * hs

theorem row_zero : m = f4 s + (f1 s u + f3 s u) * coeffA m s u + f2 s * coeffB m s := by
  unfold f4 f1 f3 coeffA f2 coeffB
  linear_combination (m^2*s^2/40 + 3*m^2*s/16 + 5*m^2/16 - 3*m*s^2/40 - 43*m*s/80 - 13*m/16 - s^2/80 - s/8 - 5/16) * hu + (m^2*s/20 - 13*m^2/8 - 3*m*s/20 + 167*m/40 - s/40 + 13/8) * hs

theorem row_one : m * coeffA m s u = f1 s u + f3 s u + f2 s * coeffA m s u + f1 s u * coeffB m s := by
  unfold coeffA f1 f3 f2 coeffB
  linear_combination (-s*u/2 - 5*u/4) * hm + (-m^2*u/40 - 19*m*u/20 + 19*u/40) * hs

theorem row_two : m * coeffB m s = 2 * f2 s + 2 * f1 s u * coeffA m s u := by
  unfold coeffB f2 f1 coeffA
  linear_combination (9*s/2 + 10) * hm + (-m^2*s^2/20 + m^2*s/8 + 5*m^2/8 + 3*m*s^2/20 - 17*m*s/40 - 13*m/8 + s^2/40 - 5/8) * hu + (-m^2*s/10 + 17*m^2/4 + 3*m*s/10 - 59*m/20 + s/20 - 139/20) * hs


variable (hspos : 0 < s) (hupos : 0 < u) (hmthree : 3 < m)
include hspos hupos hmthree

theorem s_bounds : 2 < s ∧ s < 3 := by
  constructor <;> nlinarith

theorem u_gt_three : 3 < u := by
  nlinarith

theorem f1_pos : 0 < f1 s u := by
  have hb := s_bounds m s u hs hu hm hspos hupos hmthree
  have hsub : 0 < 5 - s := by linarith [hb.2]
  unfold f1
  positivity

theorem f2_bounds : 0 < f2 s ∧ f2 s < 1 := by
  have hb := s_bounds m s u hs hu hm hspos hupos hmthree
  unfold f2
  constructor <;> linarith

theorem f3_pos : 0 < f3 s u := by
  unfold f3
  positivity

theorem f4_pos : 0 < f4 s := by
  unfold f4
  positivity

theorem f1_lt_one : f1 s u < 1 := by
  have h1 := f1_mul_u m s u hs hu hm
  have h2 := u_gt_three m s u hs hu hm hspos hupos hmthree
  have hp := f1_pos m s u hs hu hm hspos hupos hmthree
  nlinarith

theorem schmidtDenom_gt_four : 4 < schmidtDenom m s u := by
  have h1 := f1_lt_one m s u hs hu hm hspos hupos hmthree
  have h1p := f1_pos m s u hs hu hm hspos hupos hmthree
  have h2 := f2_bounds m s u hs hu hm hspos hupos hmthree
  have ht : 2 < m - f2 s := by linarith
  have hmpos : 0 < m := by linarith
  have hprod : 6 < m * (m - f2 s) := by
    calc
      6 = 3 * 2 := by norm_num
      _ < m * 2 := by nlinarith
      _ < m * (m - f2 s) := mul_lt_mul_of_pos_left ht hmpos
  unfold schmidtDenom
  nlinarith

theorem schmidtNumer_pos : 0 < schmidtNumer m s u := by
  have h1 := f1_pos m s u hs hu hm hspos hupos hmthree
  have h2 := (f2_bounds m s u hs hu hm hspos hupos hmthree).1
  have h3 := f3_pos m s u hs hu hm hspos hupos hmthree
  have hmpos : 0 < m := by linarith
  unfold schmidtNumer
  positivity

theorem coeffA_eq_formula : coeffA m s u = schmidtNumer m s u / schmidtDenom m s u := by
  have hd := schmidtDenom_gt_four m s u hs hu hm hspos hupos hmthree
  apply (eq_div_iff (by linarith : schmidtDenom m s u ≠ 0)).2
  exact coeffA_mul_denom m s u hs hu hm

theorem coeffA_pos : 0 < coeffA m s u := by
  rw [coeffA_eq_formula m s u hs hu hm hspos hupos hmthree]
  exact div_pos (schmidtNumer_pos m s u hs hu hm hspos hupos hmthree)
    (lt_trans (by norm_num) (schmidtDenom_gt_four m s u hs hu hm hspos hupos hmthree))

theorem coeffB_eq_formula : coeffB m s = 2 * (f2 s + f1 s u * coeffA m s u) / m := by
  have hmne : m ≠ 0 := by linarith
  apply (eq_div_iff hmne).2
  have h := row_two m s u hs hu hm
  nlinarith only [h]

theorem coeffB_pos : 0 < coeffB m s := by
  rw [coeffB_eq_formula m s u hs hu hm hspos hupos hmthree]
  have h1 := f1_pos m s u hs hu hm hspos hupos hmthree
  have h2 := (f2_bounds m s u hs hu hm hspos hupos hmthree).1
  have ha := coeffA_pos m s u hs hu hm hspos hupos hmthree
  have hmpos : 0 < m := by linarith
  positivity

theorem schmidtNormSq_pos : 0 < 2 + 2 * (coeffA m s u)^2 + (coeffB m s)^2 := by
  positivity

end
end CGLMP5.Attainment
