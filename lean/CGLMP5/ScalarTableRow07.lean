import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_7_0 (k : Fin 24) : mulCoeff 7 0 k = (![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_1 (k : Fin 24) : mulCoeff 7 1 k = (![0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_2 (k : Fin 24) : mulCoeff 7 2 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_3 (k : Fin 24) : mulCoeff 7 3 k = (![0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_4 (k : Fin 24) : mulCoeff 7 4 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_5 (k : Fin 24) : mulCoeff 7 5 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_6 (k : Fin 24) : mulCoeff 7 6 k = (![10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_7 (k : Fin 24) : mulCoeff 7 7 k = (![50, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_8 (k : Fin 24) : mulCoeff 7 8 k = (![0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_9 (k : Fin 24) : mulCoeff 7 9 k = (![0, 0, 50, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_10 (k : Fin 24) : mulCoeff 7 10 k = (![0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_11 (k : Fin 24) : mulCoeff 7 11 k = (![0, 0, 0, 0, 50, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_12 (k : Fin 24) : mulCoeff 7 12 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_13 (k : Fin 24) : mulCoeff 7 13 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_14 (k : Fin 24) : mulCoeff 7 14 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_15 (k : Fin 24) : mulCoeff 7 15 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_16 (k : Fin 24) : mulCoeff 7 16 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_17 (k : Fin 24) : mulCoeff 7 17 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_18 (k : Fin 24) : mulCoeff 7 18 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_19 (k : Fin 24) : mulCoeff 7 19 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_20 (k : Fin 24) : mulCoeff 7 20 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_21 (k : Fin 24) : mulCoeff 7 21 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 10, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_22 (k : Fin 24) : mulCoeff 7 22 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_7_23 (k : Fin 24) : mulCoeff 7 23 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 10, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_7 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 7 j k : ℂ)*basisEval k) = basisEval 7*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 7 0 k : ℂ)*basisEval k) = basisEval 7*basisEval 0
    simp only [coeff_7_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 7 1 k : ℂ)*basisEval k) = basisEval 7*basisEval 1
    simp only [coeff_7_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((u : ℂ)) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 2 k : ℂ)*basisEval k) = basisEval 7*basisEval 2
    simp only [coeff_7_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 7 3 k : ℂ)*basisEval k) = basisEval 7*basisEval 3
    simp only [coeff_7_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*(u : ℂ)) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 4 k : ℂ)*basisEval k) = basisEval 7*basisEval 4
    simp only [coeff_7_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 7 5 k : ℂ)*basisEval k) = basisEval 7*basisEval 5
    simp only [coeff_7_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 6 k : ℂ)*basisEval k) = basisEval 7*basisEval 6
    simp only [coeff_7_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*1) * sC_sq + -((s : ℂ)) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 7 k : ℂ)*basisEval k) = basisEval 7*basisEval 7
    simp only [coeff_7_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*1 + (2)*(s : ℂ)) * sC_sq + -((s : ℂ)^2) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 8 k : ℂ)*basisEval k) = basisEval 7*basisEval 8
    simp only [coeff_7_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)) * sC_sq + -((s : ℂ)*(x : ℂ)) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 9 k : ℂ)*basisEval k) = basisEval 7*basisEval 9
    simp only [coeff_7_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*(x : ℂ) + (2)*(s : ℂ)*(x : ℂ)) * sC_sq + -((s : ℂ)^2*(x : ℂ)) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 10 k : ℂ)*basisEval k) = basisEval 7*basisEval 10
    simp only [coeff_7_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)^2) * sC_sq + -((s : ℂ)*(x : ℂ)^2) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 11 k : ℂ)*basisEval k) = basisEval 7*basisEval 11
    simp only [coeff_7_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*(x : ℂ)^2 + (2)*(s : ℂ)*(x : ℂ)^2) * sC_sq + -((s : ℂ)^2*(x : ℂ)^2) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 12 k : ℂ)*basisEval k) = basisEval 7*basisEval 12
    simp only [coeff_7_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 7 13 k : ℂ)*basisEval k) = basisEval 7*basisEval 13
    simp only [coeff_7_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 14 k : ℂ)*basisEval k) = basisEval 7*basisEval 14
    simp only [coeff_7_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 7 15 k : ℂ)*basisEval k) = basisEval 7*basisEval 15
    simp only [coeff_7_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*(u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 16 k : ℂ)*basisEval k) = basisEval 7*basisEval 16
    simp only [coeff_7_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 7 17 k : ℂ)*basisEval k) = basisEval 7*basisEval 17
    simp only [coeff_7_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 18 k : ℂ)*basisEval k) = basisEval 7*basisEval 18
    simp only [coeff_7_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*Complex.I) * sC_sq + -((s : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 19 k : ℂ)*basisEval k) = basisEval 7*basisEval 19
    simp only [coeff_7_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*Complex.I + (2)*(s : ℂ)*Complex.I) * sC_sq + -((s : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 20 k : ℂ)*basisEval k) = basisEval 7*basisEval 20
    simp only [coeff_7_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 21 k : ℂ)*basisEval k) = basisEval 7*basisEval 21
    simp only [coeff_7_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*(x : ℂ)*Complex.I + (2)*(s : ℂ)*(x : ℂ)*Complex.I) * sC_sq + -((s : ℂ)^2*(x : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 22 k : ℂ)*basisEval k) = basisEval 7*basisEval 22
    simp only [coeff_7_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 7 23 k : ℂ)*basisEval k) = basisEval 7*basisEval 23
    simp only [coeff_7_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*(x : ℂ)^2*Complex.I + (2)*(s : ℂ)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)^2*(x : ℂ)^2*Complex.I) * uC_sq

end CGLMP5.Scalar
