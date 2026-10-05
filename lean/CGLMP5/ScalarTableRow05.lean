import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_5_0 (k : Fin 24) : mulCoeff 5 0 k = (![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_1 (k : Fin 24) : mulCoeff 5 1 k = (![0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_2 (k : Fin 24) : mulCoeff 5 2 k = (![-1000, 500, -100, 100, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_3 (k : Fin 24) : mulCoeff 5 3 k = (![2500, -1000, 500, -100, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_4 (k : Fin 24) : mulCoeff 5 4 k = (![12500, -5000, 1500, 0, -100, 225, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_5 (k : Fin 24) : mulCoeff 5 5 k = (![-25000, 12500, 0, 1500, 1125, -100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_6 (k : Fin 24) : mulCoeff 5 6 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_7 (k : Fin 24) : mulCoeff 5 7 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_8 (k : Fin 24) : mulCoeff 5 8 k = (![0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_9 (k : Fin 24) : mulCoeff 5 9 k = (![0, 0, 0, 0, 0, 0, 2500, -1000, 500, -100, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_10 (k : Fin 24) : mulCoeff 5 10 k = (![0, 0, 0, 0, 0, 0, 12500, -5000, 1500, 0, -100, 225, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_11 (k : Fin 24) : mulCoeff 5 11 k = (![0, 0, 0, 0, 0, 0, -25000, 12500, 0, 1500, 1125, -100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_12 (k : Fin 24) : mulCoeff 5 12 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_13 (k : Fin 24) : mulCoeff 5 13 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_14 (k : Fin 24) : mulCoeff 5 14 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_15 (k : Fin 24) : mulCoeff 5 15 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2500, -1000, 500, -100, 0, 25, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_16 (k : Fin 24) : mulCoeff 5 16 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12500, -5000, 1500, 0, -100, 225, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_17 (k : Fin 24) : mulCoeff 5 17 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -25000, 12500, 0, 1500, 1125, -100, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_18 (k : Fin 24) : mulCoeff 5 18 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_19 (k : Fin 24) : mulCoeff 5 19 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_20 (k : Fin 24) : mulCoeff 5 20 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_21 (k : Fin 24) : mulCoeff 5 21 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2500, -1000, 500, -100, 0, 25] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_22 (k : Fin 24) : mulCoeff 5 22 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12500, -5000, 1500, 0, -100, 225] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_5_23 (k : Fin 24) : mulCoeff 5 23 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -25000, 12500, 0, 1500, 1125, -100] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_5 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 5 j k : ℂ)*basisEval k) = basisEval 5*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 5 0 k : ℂ)*basisEval k) = basisEval 5*basisEval 0
    simp only [coeff_5_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 5 1 k : ℂ)*basisEval k) = basisEval 5*basisEval 1
    simp only [coeff_5_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 5 2 k : ℂ)*basisEval k) = basisEval 5*basisEval 2
    simp only [coeff_5_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*1 + (-20)*(x : ℂ) + (5)*(x : ℂ)^2) * sC_sq + -((s : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 3 k : ℂ)*basisEval k) = basisEval 5*basisEval 3
    simp only [coeff_5_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((500)*1 + (100)*(x : ℂ) + (-200)*(s : ℂ) + (-20)*(s : ℂ)*(x : ℂ) + (5)*(s : ℂ)*(x : ℂ)^2) * sC_sq + -((s : ℂ)^2) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 4 k : ℂ)*basisEval k) = basisEval 5*basisEval 4
    simp only [coeff_5_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2500)*1 + (300)*(x : ℂ) + (-20)*(x : ℂ)^2 + (-1000)*(s : ℂ) + (-100)*(s : ℂ)*(x : ℂ) + (25)*(s : ℂ)*(x : ℂ)^2) * sC_sq + -((s : ℂ)*(x : ℂ) + (5)*(s : ℂ)^2) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 5 k : ℂ)*basisEval k) = basisEval 5*basisEval 5
    simp only [coeff_5_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-5000)*1 + (225)*(x : ℂ)^2 + (2500)*(s : ℂ) + (300)*(s : ℂ)*(x : ℂ) + (-20)*(s : ℂ)*(x : ℂ)^2 + (-1000)*(s : ℂ)^2 + (-100)*(s : ℂ)^2*(x : ℂ) + (25)*(s : ℂ)^2*(x : ℂ)^2) * sC_sq + -((s : ℂ)^2*(x : ℂ) + (5)*(s : ℂ)^3) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 6 k : ℂ)*basisEval k) = basisEval 5*basisEval 6
    simp only [coeff_5_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 5 7 k : ℂ)*basisEval k) = basisEval 5*basisEval 7
    simp only [coeff_5_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 5 8 k : ℂ)*basisEval k) = basisEval 5*basisEval 8
    simp only [coeff_5_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*(u : ℂ) + (-20)*(x : ℂ)*(u : ℂ) + (5)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 9 k : ℂ)*basisEval k) = basisEval 5*basisEval 9
    simp only [coeff_5_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((500)*(u : ℂ) + (100)*(x : ℂ)*(u : ℂ) + (-200)*(s : ℂ)*(u : ℂ) + (-20)*(s : ℂ)*(x : ℂ)*(u : ℂ) + (5)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)^2*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 10 k : ℂ)*basisEval k) = basisEval 5*basisEval 10
    simp only [coeff_5_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2500)*(u : ℂ) + (300)*(x : ℂ)*(u : ℂ) + (-20)*(x : ℂ)^2*(u : ℂ) + (-1000)*(s : ℂ)*(u : ℂ) + (-100)*(s : ℂ)*(x : ℂ)*(u : ℂ) + (25)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)*(x : ℂ)*(u : ℂ) + (5)*(s : ℂ)^2*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 11 k : ℂ)*basisEval k) = basisEval 5*basisEval 11
    simp only [coeff_5_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-5000)*(u : ℂ) + (225)*(x : ℂ)^2*(u : ℂ) + (2500)*(s : ℂ)*(u : ℂ) + (300)*(s : ℂ)*(x : ℂ)*(u : ℂ) + (-20)*(s : ℂ)*(x : ℂ)^2*(u : ℂ) + (-1000)*(s : ℂ)^2*(u : ℂ) + (-100)*(s : ℂ)^2*(x : ℂ)*(u : ℂ) + (25)*(s : ℂ)^2*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)^2*(x : ℂ)*(u : ℂ) + (5)*(s : ℂ)^3*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 12 k : ℂ)*basisEval k) = basisEval 5*basisEval 12
    simp only [coeff_5_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 5 13 k : ℂ)*basisEval k) = basisEval 5*basisEval 13
    simp only [coeff_5_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 5 14 k : ℂ)*basisEval k) = basisEval 5*basisEval 14
    simp only [coeff_5_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*Complex.I + (-20)*(x : ℂ)*Complex.I + (5)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 15 k : ℂ)*basisEval k) = basisEval 5*basisEval 15
    simp only [coeff_5_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((500)*Complex.I + (100)*(x : ℂ)*Complex.I + (-200)*(s : ℂ)*Complex.I + (-20)*(s : ℂ)*(x : ℂ)*Complex.I + (5)*(s : ℂ)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)^2*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 16 k : ℂ)*basisEval k) = basisEval 5*basisEval 16
    simp only [coeff_5_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2500)*Complex.I + (300)*(x : ℂ)*Complex.I + (-20)*(x : ℂ)^2*Complex.I + (-1000)*(s : ℂ)*Complex.I + (-100)*(s : ℂ)*(x : ℂ)*Complex.I + (25)*(s : ℂ)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)*Complex.I + (5)*(s : ℂ)^2*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 17 k : ℂ)*basisEval k) = basisEval 5*basisEval 17
    simp only [coeff_5_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-5000)*Complex.I + (225)*(x : ℂ)^2*Complex.I + (2500)*(s : ℂ)*Complex.I + (300)*(s : ℂ)*(x : ℂ)*Complex.I + (-20)*(s : ℂ)*(x : ℂ)^2*Complex.I + (-1000)*(s : ℂ)^2*Complex.I + (-100)*(s : ℂ)^2*(x : ℂ)*Complex.I + (25)*(s : ℂ)^2*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)^2*(x : ℂ)*Complex.I + (5)*(s : ℂ)^3*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 18 k : ℂ)*basisEval k) = basisEval 5*basisEval 18
    simp only [coeff_5_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 5 19 k : ℂ)*basisEval k) = basisEval 5*basisEval 19
    simp only [coeff_5_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 5 20 k : ℂ)*basisEval k) = basisEval 5*basisEval 20
    simp only [coeff_5_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*(u : ℂ)*Complex.I + (-20)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 21 k : ℂ)*basisEval k) = basisEval 5*basisEval 21
    simp only [coeff_5_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((500)*(u : ℂ)*Complex.I + (100)*(x : ℂ)*(u : ℂ)*Complex.I + (-200)*(s : ℂ)*(u : ℂ)*Complex.I + (-20)*(s : ℂ)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)^2*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 22 k : ℂ)*basisEval k) = basisEval 5*basisEval 22
    simp only [coeff_5_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2500)*(u : ℂ)*Complex.I + (300)*(x : ℂ)*(u : ℂ)*Complex.I + (-20)*(x : ℂ)^2*(u : ℂ)*Complex.I + (-1000)*(s : ℂ)*(u : ℂ)*Complex.I + (-100)*(s : ℂ)*(x : ℂ)*(u : ℂ)*Complex.I + (25)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(s : ℂ)^2*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 5 23 k : ℂ)*basisEval k) = basisEval 5*basisEval 23
    simp only [coeff_5_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-5000)*(u : ℂ)*Complex.I + (225)*(x : ℂ)^2*(u : ℂ)*Complex.I + (2500)*(s : ℂ)*(u : ℂ)*Complex.I + (300)*(s : ℂ)*(x : ℂ)*(u : ℂ)*Complex.I + (-20)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)*Complex.I + (-1000)*(s : ℂ)^2*(u : ℂ)*Complex.I + (-100)*(s : ℂ)^2*(x : ℂ)*(u : ℂ)*Complex.I + (25)*(s : ℂ)^2*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)^2*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(s : ℂ)^3*(u : ℂ)*Complex.I) * xC_cubic

end CGLMP5.Scalar
