import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_11_0 (k : Fin 24) : mulCoeff 11 0 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_1 (k : Fin 24) : mulCoeff 11 1 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_2 (k : Fin 24) : mulCoeff 11 2 k = (![0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_3 (k : Fin 24) : mulCoeff 11 3 k = (![0, 0, 0, 0, 0, 0, 2500, -1000, 500, -100, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_4 (k : Fin 24) : mulCoeff 11 4 k = (![0, 0, 0, 0, 0, 0, 12500, -5000, 1500, 0, -100, 225, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_5 (k : Fin 24) : mulCoeff 11 5 k = (![0, 0, 0, 0, 0, 0, -25000, 12500, 0, 1500, 1125, -100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_6 (k : Fin 24) : mulCoeff 11 6 k = (![0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_7 (k : Fin 24) : mulCoeff 11 7 k = (![0, 0, 0, 0, 50, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_8 (k : Fin 24) : mulCoeff 11 8 k = (![-5000, 3000, 0, 800, 250, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_9 (k : Fin 24) : mulCoeff 11 9 k = (![15000, -5000, 4000, 0, 250, 250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_10 (k : Fin 24) : mulCoeff 11 10 k = (![75000, -25000, 15000, 3000, 1250, 2050, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_11 (k : Fin 24) : mulCoeff 11 11 k = (![-125000, 75000, 15000, 15000, 10250, 1250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_12 (k : Fin 24) : mulCoeff 11 12 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_13 (k : Fin 24) : mulCoeff 11 13 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_14 (k : Fin 24) : mulCoeff 11 14 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_15 (k : Fin 24) : mulCoeff 11 15 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2500, -1000, 500, -100, 0, 25] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_16 (k : Fin 24) : mulCoeff 11 16 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12500, -5000, 1500, 0, -100, 225] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_17 (k : Fin 24) : mulCoeff 11 17 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -25000, 12500, 0, 1500, 1125, -100] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_18 (k : Fin 24) : mulCoeff 11 18 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_19 (k : Fin 24) : mulCoeff 11 19 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 10, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_20 (k : Fin 24) : mulCoeff 11 20 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5000, 3000, 0, 800, 250, 50, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_21 (k : Fin 24) : mulCoeff 11 21 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15000, -5000, 4000, 0, 250, 250, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_22 (k : Fin 24) : mulCoeff 11 22 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75000, -25000, 15000, 3000, 1250, 2050, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_11_23 (k : Fin 24) : mulCoeff 11 23 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -125000, 75000, 15000, 15000, 10250, 1250, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_11 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 11 j k : ℂ)*basisEval k) = basisEval 11*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 11 0 k : ℂ)*basisEval k) = basisEval 11*basisEval 0
    simp only [coeff_11_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 11 1 k : ℂ)*basisEval k) = basisEval 11*basisEval 1
    simp only [coeff_11_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 11 2 k : ℂ)*basisEval k) = basisEval 11*basisEval 2
    simp only [coeff_11_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*(u : ℂ) + (-20)*(x : ℂ)*(u : ℂ) + (5)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 11 3 k : ℂ)*basisEval k) = basisEval 11*basisEval 3
    simp only [coeff_11_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((500)*(u : ℂ) + (100)*(x : ℂ)*(u : ℂ) + (-200)*(s : ℂ)*(u : ℂ) + (-20)*(s : ℂ)*(x : ℂ)*(u : ℂ) + (5)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)^2*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 11 4 k : ℂ)*basisEval k) = basisEval 11*basisEval 4
    simp only [coeff_11_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2500)*(u : ℂ) + (300)*(x : ℂ)*(u : ℂ) + (-20)*(x : ℂ)^2*(u : ℂ) + (-1000)*(s : ℂ)*(u : ℂ) + (-100)*(s : ℂ)*(x : ℂ)*(u : ℂ) + (25)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)*(x : ℂ)*(u : ℂ) + (5)*(s : ℂ)^2*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 11 5 k : ℂ)*basisEval k) = basisEval 11*basisEval 5
    simp only [coeff_11_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-5000)*(u : ℂ) + (225)*(x : ℂ)^2*(u : ℂ) + (2500)*(s : ℂ)*(u : ℂ) + (300)*(s : ℂ)*(x : ℂ)*(u : ℂ) + (-20)*(s : ℂ)*(x : ℂ)^2*(u : ℂ) + (-1000)*(s : ℂ)^2*(u : ℂ) + (-100)*(s : ℂ)^2*(x : ℂ)*(u : ℂ) + (25)*(s : ℂ)^2*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)^2*(x : ℂ)*(u : ℂ) + (5)*(s : ℂ)^3*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 11 6 k : ℂ)*basisEval k) = basisEval 11*basisEval 6
    simp only [coeff_11_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)^2) * sC_sq + -((s : ℂ)*(x : ℂ)^2) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 11 7 k : ℂ)*basisEval k) = basisEval 11*basisEval 7
    simp only [coeff_11_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*(x : ℂ)^2 + (2)*(s : ℂ)*(x : ℂ)^2) * sC_sq + -((s : ℂ)^2*(x : ℂ)^2) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 11 8 k : ℂ)*basisEval k) = basisEval 11*basisEval 8
    simp only [coeff_11_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1000)*1 + (50)*(x : ℂ)^2 + (-400)*(s : ℂ) + (-40)*(s : ℂ)*(x : ℂ) + (10)*(s : ℂ)*(x : ℂ)^2) * sC_sq + -((10)*(s : ℂ) + (2)*(s : ℂ)^2) * xC_cubic + -((s : ℂ)*(x : ℂ)^3) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 11 9 k : ℂ)*basisEval k) = basisEval 11*basisEval 9
    simp only [coeff_11_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((3000)*1 + (800)*(x : ℂ) + (50)*(x : ℂ)^2 + (-1000)*(s : ℂ) + (50)*(s : ℂ)*(x : ℂ)^2 + (-400)*(s : ℂ)^2 + (-40)*(s : ℂ)^2*(x : ℂ) + (10)*(s : ℂ)^2*(x : ℂ)^2) * sC_sq + -((10)*(s : ℂ)^2 + (2)*(s : ℂ)^3) * xC_cubic + -((s : ℂ)^2*(x : ℂ)^3) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 11 10 k : ℂ)*basisEval k) = basisEval 11*basisEval 10
    simp only [coeff_11_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((15000)*1 + (3000)*(x : ℂ) + (250)*(x : ℂ)^2 + (-5000)*(s : ℂ) + (-400)*(s : ℂ)*(x : ℂ) + (210)*(s : ℂ)*(x : ℂ)^2 + (-2000)*(s : ℂ)^2 + (-200)*(s : ℂ)^2*(x : ℂ) + (50)*(s : ℂ)^2*(x : ℂ)^2) * sC_sq + -((10)*(s : ℂ)*(x : ℂ) + (50)*(s : ℂ)^2 + (2)*(s : ℂ)^2*(x : ℂ) + (10)*(s : ℂ)^3) * xC_cubic + -((s : ℂ)*(x : ℂ)^4) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 11 11 k : ℂ)*basisEval k) = basisEval 11*basisEval 11
    simp only [coeff_11_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-25000)*1 + (3000)*(x : ℂ) + (2050)*(x : ℂ)^2 + (15000)*(s : ℂ) + (3000)*(s : ℂ)*(x : ℂ) + (250)*(s : ℂ)*(x : ℂ)^2 + (-5000)*(s : ℂ)^2 + (-400)*(s : ℂ)^2*(x : ℂ) + (210)*(s : ℂ)^2*(x : ℂ)^2 + (-2000)*(s : ℂ)^3 + (-200)*(s : ℂ)^3*(x : ℂ) + (50)*(s : ℂ)^3*(x : ℂ)^2) * sC_sq + -((10)*(s : ℂ)^2*(x : ℂ) + (50)*(s : ℂ)^3 + (2)*(s : ℂ)^3*(x : ℂ) + (10)*(s : ℂ)^4) * xC_cubic + -((s : ℂ)^2*(x : ℂ)^4) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 11 12 k : ℂ)*basisEval k) = basisEval 11*basisEval 12
    simp only [coeff_11_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 11 13 k : ℂ)*basisEval k) = basisEval 11*basisEval 13
    simp only [coeff_11_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 11 14 k : ℂ)*basisEval k) = basisEval 11*basisEval 14
    simp only [coeff_11_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*(u : ℂ)*Complex.I + (-20)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 11 15 k : ℂ)*basisEval k) = basisEval 11*basisEval 15
    simp only [coeff_11_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((500)*(u : ℂ)*Complex.I + (100)*(x : ℂ)*(u : ℂ)*Complex.I + (-200)*(s : ℂ)*(u : ℂ)*Complex.I + (-20)*(s : ℂ)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)^2*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 11 16 k : ℂ)*basisEval k) = basisEval 11*basisEval 16
    simp only [coeff_11_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2500)*(u : ℂ)*Complex.I + (300)*(x : ℂ)*(u : ℂ)*Complex.I + (-20)*(x : ℂ)^2*(u : ℂ)*Complex.I + (-1000)*(s : ℂ)*(u : ℂ)*Complex.I + (-100)*(s : ℂ)*(x : ℂ)*(u : ℂ)*Complex.I + (25)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(s : ℂ)^2*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 11 17 k : ℂ)*basisEval k) = basisEval 11*basisEval 17
    simp only [coeff_11_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-5000)*(u : ℂ)*Complex.I + (225)*(x : ℂ)^2*(u : ℂ)*Complex.I + (2500)*(s : ℂ)*(u : ℂ)*Complex.I + (300)*(s : ℂ)*(x : ℂ)*(u : ℂ)*Complex.I + (-20)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)*Complex.I + (-1000)*(s : ℂ)^2*(u : ℂ)*Complex.I + (-100)*(s : ℂ)^2*(x : ℂ)*(u : ℂ)*Complex.I + (25)*(s : ℂ)^2*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)^2*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(s : ℂ)^3*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 11 18 k : ℂ)*basisEval k) = basisEval 11*basisEval 18
    simp only [coeff_11_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 11 19 k : ℂ)*basisEval k) = basisEval 11*basisEval 19
    simp only [coeff_11_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*(x : ℂ)^2*Complex.I + (2)*(s : ℂ)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)^2*(x : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 11 20 k : ℂ)*basisEval k) = basisEval 11*basisEval 20
    simp only [coeff_11_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1000)*Complex.I + (50)*(x : ℂ)^2*Complex.I + (-400)*(s : ℂ)*Complex.I + (-40)*(s : ℂ)*(x : ℂ)*Complex.I + (10)*(s : ℂ)*(x : ℂ)^2*Complex.I) * sC_sq + -((10)*(s : ℂ)*Complex.I + (2)*(s : ℂ)^2*Complex.I) * xC_cubic + -((s : ℂ)*(x : ℂ)^3*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 11 21 k : ℂ)*basisEval k) = basisEval 11*basisEval 21
    simp only [coeff_11_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((3000)*Complex.I + (800)*(x : ℂ)*Complex.I + (50)*(x : ℂ)^2*Complex.I + (-1000)*(s : ℂ)*Complex.I + (50)*(s : ℂ)*(x : ℂ)^2*Complex.I + (-400)*(s : ℂ)^2*Complex.I + (-40)*(s : ℂ)^2*(x : ℂ)*Complex.I + (10)*(s : ℂ)^2*(x : ℂ)^2*Complex.I) * sC_sq + -((10)*(s : ℂ)^2*Complex.I + (2)*(s : ℂ)^3*Complex.I) * xC_cubic + -((s : ℂ)^2*(x : ℂ)^3*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 11 22 k : ℂ)*basisEval k) = basisEval 11*basisEval 22
    simp only [coeff_11_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((15000)*Complex.I + (3000)*(x : ℂ)*Complex.I + (250)*(x : ℂ)^2*Complex.I + (-5000)*(s : ℂ)*Complex.I + (-400)*(s : ℂ)*(x : ℂ)*Complex.I + (210)*(s : ℂ)*(x : ℂ)^2*Complex.I + (-2000)*(s : ℂ)^2*Complex.I + (-200)*(s : ℂ)^2*(x : ℂ)*Complex.I + (50)*(s : ℂ)^2*(x : ℂ)^2*Complex.I) * sC_sq + -((10)*(s : ℂ)*(x : ℂ)*Complex.I + (50)*(s : ℂ)^2*Complex.I + (2)*(s : ℂ)^2*(x : ℂ)*Complex.I + (10)*(s : ℂ)^3*Complex.I) * xC_cubic + -((s : ℂ)*(x : ℂ)^4*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 11 23 k : ℂ)*basisEval k) = basisEval 11*basisEval 23
    simp only [coeff_11_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-25000)*Complex.I + (3000)*(x : ℂ)*Complex.I + (2050)*(x : ℂ)^2*Complex.I + (15000)*(s : ℂ)*Complex.I + (3000)*(s : ℂ)*(x : ℂ)*Complex.I + (250)*(s : ℂ)*(x : ℂ)^2*Complex.I + (-5000)*(s : ℂ)^2*Complex.I + (-400)*(s : ℂ)^2*(x : ℂ)*Complex.I + (210)*(s : ℂ)^2*(x : ℂ)^2*Complex.I + (-2000)*(s : ℂ)^3*Complex.I + (-200)*(s : ℂ)^3*(x : ℂ)*Complex.I + (50)*(s : ℂ)^3*(x : ℂ)^2*Complex.I) * sC_sq + -((10)*(s : ℂ)^2*(x : ℂ)*Complex.I + (50)*(s : ℂ)^3*Complex.I + (2)*(s : ℂ)^3*(x : ℂ)*Complex.I + (10)*(s : ℂ)^4*Complex.I) * xC_cubic + -((s : ℂ)^2*(x : ℂ)^4*Complex.I) * uC_sq

end CGLMP5.Scalar
