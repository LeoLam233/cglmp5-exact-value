import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_20_0 (k : Fin 24) : mulCoeff 20 0 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_1 (k : Fin 24) : mulCoeff 20 1 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_2 (k : Fin 24) : mulCoeff 20 2 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_3 (k : Fin 24) : mulCoeff 20 3 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_4 (k : Fin 24) : mulCoeff 20 4 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500, -200, 100, -20, 0, 5] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_5 (k : Fin 24) : mulCoeff 20 5 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_6 (k : Fin 24) : mulCoeff 20 6 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_7 (k : Fin 24) : mulCoeff 20 7 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_8 (k : Fin 24) : mulCoeff 20 8 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 2, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_9 (k : Fin 24) : mulCoeff 20 9 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_10 (k : Fin 24) : mulCoeff 20 10 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3000, -1000, 800, 0, 50, 50, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_11 (k : Fin 24) : mulCoeff 20 11 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5000, 3000, 0, 800, 250, 50, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_12 (k : Fin 24) : mulCoeff 20 12 k = (![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_13 (k : Fin 24) : mulCoeff 20 13 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_14 (k : Fin 24) : mulCoeff 20 14 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_15 (k : Fin 24) : mulCoeff 20 15 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_16 (k : Fin 24) : mulCoeff 20 16 k = (![0, 0, 0, 0, 0, 0, -500, 200, -100, 20, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_17 (k : Fin 24) : mulCoeff 20 17 k = (![0, 0, 0, 0, 0, 0, 1000, -500, 100, -100, -25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_18 (k : Fin 24) : mulCoeff 20 18 k = (![0, 0, -10, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_19 (k : Fin 24) : mulCoeff 20 19 k = (![0, 0, -10, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_20 (k : Fin 24) : mulCoeff 20 20 k = (![0, 0, 0, 0, -10, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_21 (k : Fin 24) : mulCoeff 20 21 k = (![0, 0, 0, 0, -10, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_22 (k : Fin 24) : mulCoeff 20 22 k = (![-3000, 1000, -800, 0, -50, -50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_20_23 (k : Fin 24) : mulCoeff 20 23 k = (![5000, -3000, 0, -800, -250, -50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_20 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 20 j k : ℂ)*basisEval k) = basisEval 20*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 20 0 k : ℂ)*basisEval k) = basisEval 20*basisEval 0
    simp only [coeff_20_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 20 1 k : ℂ)*basisEval k) = basisEval 20*basisEval 1
    simp only [coeff_20_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 20 2 k : ℂ)*basisEval k) = basisEval 20*basisEval 2
    simp only [coeff_20_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 20 3 k : ℂ)*basisEval k) = basisEval 20*basisEval 3
    simp only [coeff_20_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 20 4 k : ℂ)*basisEval k) = basisEval 20*basisEval 4
    simp only [coeff_20_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 20 5 k : ℂ)*basisEval k) = basisEval 20*basisEval 5
    simp only [coeff_20_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*(u : ℂ)*Complex.I + (-20)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 20 6 k : ℂ)*basisEval k) = basisEval 20*basisEval 6
    simp only [coeff_20_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 20 7 k : ℂ)*basisEval k) = basisEval 20*basisEval 7
    simp only [coeff_20_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 20 8 k : ℂ)*basisEval k) = basisEval 20*basisEval 8
    simp only [coeff_20_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 20 9 k : ℂ)*basisEval k) = basisEval 20*basisEval 9
    simp only [coeff_20_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 20 10 k : ℂ)*basisEval k) = basisEval 20*basisEval 10
    simp only [coeff_20_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-400)*Complex.I + (-40)*(x : ℂ)*Complex.I + (10)*(x : ℂ)^2*Complex.I) * sC_sq + -((10)*Complex.I + (2)*(s : ℂ)*Complex.I) * xC_cubic + -((x : ℂ)^3*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 20 11 k : ℂ)*basisEval k) = basisEval 20*basisEval 11
    simp only [coeff_20_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1000)*Complex.I + (50)*(x : ℂ)^2*Complex.I + (-400)*(s : ℂ)*Complex.I + (-40)*(s : ℂ)*(x : ℂ)*Complex.I + (10)*(s : ℂ)*(x : ℂ)^2*Complex.I) * sC_sq + -((10)*(s : ℂ)*Complex.I + (2)*(s : ℂ)^2*Complex.I) * xC_cubic + -((s : ℂ)*(x : ℂ)^3*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 20 12 k : ℂ)*basisEval k) = basisEval 20*basisEval 12
    simp only [coeff_20_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 20 13 k : ℂ)*basisEval k) = basisEval 20*basisEval 13
    simp only [coeff_20_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 20 14 k : ℂ)*basisEval k) = basisEval 20*basisEval 14
    simp only [coeff_20_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 20 15 k : ℂ)*basisEval k) = basisEval 20*basisEval 15
    simp only [coeff_20_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)^2*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 20 16 k : ℂ)*basisEval k) = basisEval 20*basisEval 16
    simp only [coeff_20_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(u : ℂ)) * xC_cubic + -((x : ℂ)^3*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 20 17 k : ℂ)*basisEval k) = basisEval 20*basisEval 17
    simp only [coeff_20_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((200)*(u : ℂ) + (20)*(x : ℂ)*(u : ℂ) + (-5)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((-1)*(s : ℂ)*(u : ℂ)) * xC_cubic + -((s : ℂ)*(x : ℂ)^3*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 20 18 k : ℂ)*basisEval k) = basisEval 20*basisEval 18
    simp only [coeff_20_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(x : ℂ)) * uC_sq + -((x : ℂ)*(u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 20 19 k : ℂ)*basisEval k) = basisEval 20*basisEval 19
    simp only [coeff_20_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-2)*(x : ℂ)) * sC_sq + -((-1)*(s : ℂ)*(x : ℂ)) * uC_sq + -((s : ℂ)*(x : ℂ)*(u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 20 20 k : ℂ)*basisEval k) = basisEval 20*basisEval 20
    simp only [coeff_20_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(x : ℂ)^2) * uC_sq + -((x : ℂ)^2*(u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 20 21 k : ℂ)*basisEval k) = basisEval 20*basisEval 21
    simp only [coeff_20_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-2)*(x : ℂ)^2) * sC_sq + -((-1)*(s : ℂ)*(x : ℂ)^2) * uC_sq + -((s : ℂ)*(x : ℂ)^2*(u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 20 22 k : ℂ)*basisEval k) = basisEval 20*basisEval 22
    simp only [coeff_20_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((400)*1 + (40)*(x : ℂ) + (-10)*(x : ℂ)^2) * sC_sq + -((-10)*1 + (-2)*(s : ℂ)) * xC_cubic + -((-1)*(x : ℂ)^3) * uC_sq + -((x : ℂ)^3*(u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 20 23 k : ℂ)*basisEval k) = basisEval 20*basisEval 23
    simp only [coeff_20_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((1000)*1 + (-50)*(x : ℂ)^2 + (400)*(s : ℂ) + (40)*(s : ℂ)*(x : ℂ) + (-10)*(s : ℂ)*(x : ℂ)^2) * sC_sq + -((-10)*(s : ℂ) + (-2)*(s : ℂ)^2) * xC_cubic + -((-1)*(s : ℂ)*(x : ℂ)^3) * uC_sq + -((s : ℂ)*(x : ℂ)^3*(u : ℂ)^2) * Complex.I_sq

end CGLMP5.Scalar
