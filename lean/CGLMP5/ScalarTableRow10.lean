import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_10_0 (k : Fin 24) : mulCoeff 10 0 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_1 (k : Fin 24) : mulCoeff 10 1 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_2 (k : Fin 24) : mulCoeff 10 2 k = (![0, 0, 0, 0, 0, 0, 500, -200, 100, -20, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_3 (k : Fin 24) : mulCoeff 10 3 k = (![0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_4 (k : Fin 24) : mulCoeff 10 4 k = (![0, 0, 0, 0, 0, 0, -5000, 2500, 0, 300, 225, -20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_5 (k : Fin 24) : mulCoeff 10 5 k = (![0, 0, 0, 0, 0, 0, 12500, -5000, 1500, 0, -100, 225, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_6 (k : Fin 24) : mulCoeff 10 6 k = (![0, 0, 0, 0, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_7 (k : Fin 24) : mulCoeff 10 7 k = (![0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_8 (k : Fin 24) : mulCoeff 10 8 k = (![3000, -1000, 800, 0, 50, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_9 (k : Fin 24) : mulCoeff 10 9 k = (![-5000, 3000, 0, 800, 250, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_10 (k : Fin 24) : mulCoeff 10 10 k = (![-25000, 15000, 3000, 3000, 2050, 250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_11 (k : Fin 24) : mulCoeff 10 11 k = (![75000, -25000, 15000, 3000, 1250, 2050, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_12 (k : Fin 24) : mulCoeff 10 12 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_13 (k : Fin 24) : mulCoeff 10 13 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_14 (k : Fin 24) : mulCoeff 10 14 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500, -200, 100, -20, 0, 5] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_15 (k : Fin 24) : mulCoeff 10 15 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_16 (k : Fin 24) : mulCoeff 10 16 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5000, 2500, 0, 300, 225, -20] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_17 (k : Fin 24) : mulCoeff 10 17 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12500, -5000, 1500, 0, -100, 225] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_18 (k : Fin 24) : mulCoeff 10 18 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 2, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_19 (k : Fin 24) : mulCoeff 10 19 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_20 (k : Fin 24) : mulCoeff 10 20 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3000, -1000, 800, 0, 50, 50, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_21 (k : Fin 24) : mulCoeff 10 21 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5000, 3000, 0, 800, 250, 50, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_22 (k : Fin 24) : mulCoeff 10 22 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -25000, 15000, 3000, 3000, 2050, 250, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_10_23 (k : Fin 24) : mulCoeff 10 23 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75000, -25000, 15000, 3000, 1250, 2050, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_10 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 10 j k : ℂ)*basisEval k) = basisEval 10*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 10 0 k : ℂ)*basisEval k) = basisEval 10*basisEval 0
    simp only [coeff_10_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 10 1 k : ℂ)*basisEval k) = basisEval 10*basisEval 1
    simp only [coeff_10_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 10 2 k : ℂ)*basisEval k) = basisEval 10*basisEval 2
    simp only [coeff_10_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 10 3 k : ℂ)*basisEval k) = basisEval 10*basisEval 3
    simp only [coeff_10_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*(u : ℂ) + (-20)*(x : ℂ)*(u : ℂ) + (5)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 10 4 k : ℂ)*basisEval k) = basisEval 10*basisEval 4
    simp only [coeff_10_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1000)*(u : ℂ) + (-100)*(x : ℂ)*(u : ℂ) + (25)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((x : ℂ)*(u : ℂ) + (5)*(s : ℂ)*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 10 5 k : ℂ)*basisEval k) = basisEval 10*basisEval 5
    simp only [coeff_10_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2500)*(u : ℂ) + (300)*(x : ℂ)*(u : ℂ) + (-20)*(x : ℂ)^2*(u : ℂ) + (-1000)*(s : ℂ)*(u : ℂ) + (-100)*(s : ℂ)*(x : ℂ)*(u : ℂ) + (25)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)*(x : ℂ)*(u : ℂ) + (5)*(s : ℂ)^2*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 10 6 k : ℂ)*basisEval k) = basisEval 10*basisEval 6
    simp only [coeff_10_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 10 7 k : ℂ)*basisEval k) = basisEval 10*basisEval 7
    simp only [coeff_10_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)^2) * sC_sq + -((s : ℂ)*(x : ℂ)^2) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 10 8 k : ℂ)*basisEval k) = basisEval 10*basisEval 8
    simp only [coeff_10_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-400)*1 + (-40)*(x : ℂ) + (10)*(x : ℂ)^2) * sC_sq + -((10)*1 + (2)*(s : ℂ)) * xC_cubic + -((x : ℂ)^3) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 10 9 k : ℂ)*basisEval k) = basisEval 10*basisEval 9
    simp only [coeff_10_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1000)*1 + (50)*(x : ℂ)^2 + (-400)*(s : ℂ) + (-40)*(s : ℂ)*(x : ℂ) + (10)*(s : ℂ)*(x : ℂ)^2) * sC_sq + -((10)*(s : ℂ) + (2)*(s : ℂ)^2) * xC_cubic + -((s : ℂ)*(x : ℂ)^3) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 10 10 k : ℂ)*basisEval k) = basisEval 10*basisEval 10
    simp only [coeff_10_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-5000)*1 + (-400)*(x : ℂ) + (210)*(x : ℂ)^2 + (-2000)*(s : ℂ) + (-200)*(s : ℂ)*(x : ℂ) + (50)*(s : ℂ)*(x : ℂ)^2) * sC_sq + -((10)*(x : ℂ) + (50)*(s : ℂ) + (2)*(s : ℂ)*(x : ℂ) + (10)*(s : ℂ)^2) * xC_cubic + -((x : ℂ)^4) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 10 11 k : ℂ)*basisEval k) = basisEval 10*basisEval 11
    simp only [coeff_10_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((15000)*1 + (3000)*(x : ℂ) + (250)*(x : ℂ)^2 + (-5000)*(s : ℂ) + (-400)*(s : ℂ)*(x : ℂ) + (210)*(s : ℂ)*(x : ℂ)^2 + (-2000)*(s : ℂ)^2 + (-200)*(s : ℂ)^2*(x : ℂ) + (50)*(s : ℂ)^2*(x : ℂ)^2) * sC_sq + -((10)*(s : ℂ)*(x : ℂ) + (50)*(s : ℂ)^2 + (2)*(s : ℂ)^2*(x : ℂ) + (10)*(s : ℂ)^3) * xC_cubic + -((s : ℂ)*(x : ℂ)^4) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 10 12 k : ℂ)*basisEval k) = basisEval 10*basisEval 12
    simp only [coeff_10_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 10 13 k : ℂ)*basisEval k) = basisEval 10*basisEval 13
    simp only [coeff_10_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 10 14 k : ℂ)*basisEval k) = basisEval 10*basisEval 14
    simp only [coeff_10_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 10 15 k : ℂ)*basisEval k) = basisEval 10*basisEval 15
    simp only [coeff_10_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*(u : ℂ)*Complex.I + (-20)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 10 16 k : ℂ)*basisEval k) = basisEval 10*basisEval 16
    simp only [coeff_10_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1000)*(u : ℂ)*Complex.I + (-100)*(x : ℂ)*(u : ℂ)*Complex.I + (25)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((x : ℂ)*(u : ℂ)*Complex.I + (5)*(s : ℂ)*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 10 17 k : ℂ)*basisEval k) = basisEval 10*basisEval 17
    simp only [coeff_10_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2500)*(u : ℂ)*Complex.I + (300)*(x : ℂ)*(u : ℂ)*Complex.I + (-20)*(x : ℂ)^2*(u : ℂ)*Complex.I + (-1000)*(s : ℂ)*(u : ℂ)*Complex.I + (-100)*(s : ℂ)*(x : ℂ)*(u : ℂ)*Complex.I + (25)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(s : ℂ)^2*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 10 18 k : ℂ)*basisEval k) = basisEval 10*basisEval 18
    simp only [coeff_10_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 10 19 k : ℂ)*basisEval k) = basisEval 10*basisEval 19
    simp only [coeff_10_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 10 20 k : ℂ)*basisEval k) = basisEval 10*basisEval 20
    simp only [coeff_10_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-400)*Complex.I + (-40)*(x : ℂ)*Complex.I + (10)*(x : ℂ)^2*Complex.I) * sC_sq + -((10)*Complex.I + (2)*(s : ℂ)*Complex.I) * xC_cubic + -((x : ℂ)^3*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 10 21 k : ℂ)*basisEval k) = basisEval 10*basisEval 21
    simp only [coeff_10_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1000)*Complex.I + (50)*(x : ℂ)^2*Complex.I + (-400)*(s : ℂ)*Complex.I + (-40)*(s : ℂ)*(x : ℂ)*Complex.I + (10)*(s : ℂ)*(x : ℂ)^2*Complex.I) * sC_sq + -((10)*(s : ℂ)*Complex.I + (2)*(s : ℂ)^2*Complex.I) * xC_cubic + -((s : ℂ)*(x : ℂ)^3*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 10 22 k : ℂ)*basisEval k) = basisEval 10*basisEval 22
    simp only [coeff_10_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-5000)*Complex.I + (-400)*(x : ℂ)*Complex.I + (210)*(x : ℂ)^2*Complex.I + (-2000)*(s : ℂ)*Complex.I + (-200)*(s : ℂ)*(x : ℂ)*Complex.I + (50)*(s : ℂ)*(x : ℂ)^2*Complex.I) * sC_sq + -((10)*(x : ℂ)*Complex.I + (50)*(s : ℂ)*Complex.I + (2)*(s : ℂ)*(x : ℂ)*Complex.I + (10)*(s : ℂ)^2*Complex.I) * xC_cubic + -((x : ℂ)^4*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 10 23 k : ℂ)*basisEval k) = basisEval 10*basisEval 23
    simp only [coeff_10_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((15000)*Complex.I + (3000)*(x : ℂ)*Complex.I + (250)*(x : ℂ)^2*Complex.I + (-5000)*(s : ℂ)*Complex.I + (-400)*(s : ℂ)*(x : ℂ)*Complex.I + (210)*(s : ℂ)*(x : ℂ)^2*Complex.I + (-2000)*(s : ℂ)^2*Complex.I + (-200)*(s : ℂ)^2*(x : ℂ)*Complex.I + (50)*(s : ℂ)^2*(x : ℂ)^2*Complex.I) * sC_sq + -((10)*(s : ℂ)*(x : ℂ)*Complex.I + (50)*(s : ℂ)^2*Complex.I + (2)*(s : ℂ)^2*(x : ℂ)*Complex.I + (10)*(s : ℂ)^3*Complex.I) * xC_cubic + -((s : ℂ)*(x : ℂ)^4*Complex.I) * uC_sq

end CGLMP5.Scalar
