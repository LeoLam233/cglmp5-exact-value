import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_9_0 (k : Fin 24) : mulCoeff 9 0 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_1 (k : Fin 24) : mulCoeff 9 1 k = (![0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_2 (k : Fin 24) : mulCoeff 9 2 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_3 (k : Fin 24) : mulCoeff 9 3 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_4 (k : Fin 24) : mulCoeff 9 4 k = (![0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_5 (k : Fin 24) : mulCoeff 9 5 k = (![0, 0, 0, 0, 0, 0, 2500, -1000, 500, -100, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_6 (k : Fin 24) : mulCoeff 9 6 k = (![0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_7 (k : Fin 24) : mulCoeff 9 7 k = (![0, 0, 50, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_8 (k : Fin 24) : mulCoeff 9 8 k = (![0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_9 (k : Fin 24) : mulCoeff 9 9 k = (![0, 0, 0, 0, 50, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_10 (k : Fin 24) : mulCoeff 9 10 k = (![-5000, 3000, 0, 800, 250, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_11 (k : Fin 24) : mulCoeff 9 11 k = (![15000, -5000, 4000, 0, 250, 250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_12 (k : Fin 24) : mulCoeff 9 12 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_13 (k : Fin 24) : mulCoeff 9 13 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_14 (k : Fin 24) : mulCoeff 9 14 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_15 (k : Fin 24) : mulCoeff 9 15 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_16 (k : Fin 24) : mulCoeff 9 16 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_17 (k : Fin 24) : mulCoeff 9 17 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2500, -1000, 500, -100, 0, 25] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_18 (k : Fin 24) : mulCoeff 9 18 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_19 (k : Fin 24) : mulCoeff 9 19 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 10, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_20 (k : Fin 24) : mulCoeff 9 20 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_21 (k : Fin 24) : mulCoeff 9 21 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 10, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_22 (k : Fin 24) : mulCoeff 9 22 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5000, 3000, 0, 800, 250, 50, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_9_23 (k : Fin 24) : mulCoeff 9 23 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15000, -5000, 4000, 0, 250, 250, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_9 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 9 j k : ℂ)*basisEval k) = basisEval 9*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 9 0 k : ℂ)*basisEval k) = basisEval 9*basisEval 0
    simp only [coeff_9_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 9 1 k : ℂ)*basisEval k) = basisEval 9*basisEval 1
    simp only [coeff_9_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*(u : ℂ)) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 2 k : ℂ)*basisEval k) = basisEval 9*basisEval 2
    simp only [coeff_9_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 9 3 k : ℂ)*basisEval k) = basisEval 9*basisEval 3
    simp only [coeff_9_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 4 k : ℂ)*basisEval k) = basisEval 9*basisEval 4
    simp only [coeff_9_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*(u : ℂ) + (-20)*(x : ℂ)*(u : ℂ) + (5)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 9 5 k : ℂ)*basisEval k) = basisEval 9*basisEval 5
    simp only [coeff_9_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((500)*(u : ℂ) + (100)*(x : ℂ)*(u : ℂ) + (-200)*(s : ℂ)*(u : ℂ) + (-20)*(s : ℂ)*(x : ℂ)*(u : ℂ) + (5)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)^2*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 9 6 k : ℂ)*basisEval k) = basisEval 9*basisEval 6
    simp only [coeff_9_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)) * sC_sq + -((s : ℂ)*(x : ℂ)) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 7 k : ℂ)*basisEval k) = basisEval 9*basisEval 7
    simp only [coeff_9_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*(x : ℂ) + (2)*(s : ℂ)*(x : ℂ)) * sC_sq + -((s : ℂ)^2*(x : ℂ)) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 8 k : ℂ)*basisEval k) = basisEval 9*basisEval 8
    simp only [coeff_9_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)^2) * sC_sq + -((s : ℂ)*(x : ℂ)^2) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 9 k : ℂ)*basisEval k) = basisEval 9*basisEval 9
    simp only [coeff_9_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*(x : ℂ)^2 + (2)*(s : ℂ)*(x : ℂ)^2) * sC_sq + -((s : ℂ)^2*(x : ℂ)^2) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 10 k : ℂ)*basisEval k) = basisEval 9*basisEval 10
    simp only [coeff_9_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1000)*1 + (50)*(x : ℂ)^2 + (-400)*(s : ℂ) + (-40)*(s : ℂ)*(x : ℂ) + (10)*(s : ℂ)*(x : ℂ)^2) * sC_sq + -((10)*(s : ℂ) + (2)*(s : ℂ)^2) * xC_cubic + -((s : ℂ)*(x : ℂ)^3) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 11 k : ℂ)*basisEval k) = basisEval 9*basisEval 11
    simp only [coeff_9_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((3000)*1 + (800)*(x : ℂ) + (50)*(x : ℂ)^2 + (-1000)*(s : ℂ) + (50)*(s : ℂ)*(x : ℂ)^2 + (-400)*(s : ℂ)^2 + (-40)*(s : ℂ)^2*(x : ℂ) + (10)*(s : ℂ)^2*(x : ℂ)^2) * sC_sq + -((10)*(s : ℂ)^2 + (2)*(s : ℂ)^3) * xC_cubic + -((s : ℂ)^2*(x : ℂ)^3) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 12 k : ℂ)*basisEval k) = basisEval 9*basisEval 12
    simp only [coeff_9_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 9 13 k : ℂ)*basisEval k) = basisEval 9*basisEval 13
    simp only [coeff_9_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*(u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 14 k : ℂ)*basisEval k) = basisEval 9*basisEval 14
    simp only [coeff_9_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 9 15 k : ℂ)*basisEval k) = basisEval 9*basisEval 15
    simp only [coeff_9_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 16 k : ℂ)*basisEval k) = basisEval 9*basisEval 16
    simp only [coeff_9_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*(u : ℂ)*Complex.I + (-20)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 9 17 k : ℂ)*basisEval k) = basisEval 9*basisEval 17
    simp only [coeff_9_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((500)*(u : ℂ)*Complex.I + (100)*(x : ℂ)*(u : ℂ)*Complex.I + (-200)*(s : ℂ)*(u : ℂ)*Complex.I + (-20)*(s : ℂ)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)^2*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 9 18 k : ℂ)*basisEval k) = basisEval 9*basisEval 18
    simp only [coeff_9_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 19 k : ℂ)*basisEval k) = basisEval 9*basisEval 19
    simp only [coeff_9_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*(x : ℂ)*Complex.I + (2)*(s : ℂ)*(x : ℂ)*Complex.I) * sC_sq + -((s : ℂ)^2*(x : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 20 k : ℂ)*basisEval k) = basisEval 9*basisEval 20
    simp only [coeff_9_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 21 k : ℂ)*basisEval k) = basisEval 9*basisEval 21
    simp only [coeff_9_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*(x : ℂ)^2*Complex.I + (2)*(s : ℂ)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)^2*(x : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 22 k : ℂ)*basisEval k) = basisEval 9*basisEval 22
    simp only [coeff_9_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1000)*Complex.I + (50)*(x : ℂ)^2*Complex.I + (-400)*(s : ℂ)*Complex.I + (-40)*(s : ℂ)*(x : ℂ)*Complex.I + (10)*(s : ℂ)*(x : ℂ)^2*Complex.I) * sC_sq + -((10)*(s : ℂ)*Complex.I + (2)*(s : ℂ)^2*Complex.I) * xC_cubic + -((s : ℂ)*(x : ℂ)^3*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 9 23 k : ℂ)*basisEval k) = basisEval 9*basisEval 23
    simp only [coeff_9_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((3000)*Complex.I + (800)*(x : ℂ)*Complex.I + (50)*(x : ℂ)^2*Complex.I + (-1000)*(s : ℂ)*Complex.I + (50)*(s : ℂ)*(x : ℂ)^2*Complex.I + (-400)*(s : ℂ)^2*Complex.I + (-40)*(s : ℂ)^2*(x : ℂ)*Complex.I + (10)*(s : ℂ)^2*(x : ℂ)^2*Complex.I) * sC_sq + -((10)*(s : ℂ)^2*Complex.I + (2)*(s : ℂ)^3*Complex.I) * xC_cubic + -((s : ℂ)^2*(x : ℂ)^3*Complex.I) * uC_sq

end CGLMP5.Scalar
