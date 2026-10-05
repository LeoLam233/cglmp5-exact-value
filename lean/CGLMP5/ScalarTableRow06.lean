import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_6_0 (k : Fin 24) : mulCoeff 6 0 k = (![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_1 (k : Fin 24) : mulCoeff 6 1 k = (![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_2 (k : Fin 24) : mulCoeff 6 2 k = (![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_3 (k : Fin 24) : mulCoeff 6 3 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_4 (k : Fin 24) : mulCoeff 6 4 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_5 (k : Fin 24) : mulCoeff 6 5 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_6 (k : Fin 24) : mulCoeff 6 6 k = (![10, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_7 (k : Fin 24) : mulCoeff 6 7 k = (![10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_8 (k : Fin 24) : mulCoeff 6 8 k = (![0, 0, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_9 (k : Fin 24) : mulCoeff 6 9 k = (![0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_10 (k : Fin 24) : mulCoeff 6 10 k = (![0, 0, 0, 0, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_11 (k : Fin 24) : mulCoeff 6 11 k = (![0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_12 (k : Fin 24) : mulCoeff 6 12 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_13 (k : Fin 24) : mulCoeff 6 13 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_14 (k : Fin 24) : mulCoeff 6 14 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_15 (k : Fin 24) : mulCoeff 6 15 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_16 (k : Fin 24) : mulCoeff 6 16 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_17 (k : Fin 24) : mulCoeff 6 17 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_18 (k : Fin 24) : mulCoeff 6 18 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_19 (k : Fin 24) : mulCoeff 6 19 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_20 (k : Fin 24) : mulCoeff 6 20 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_21 (k : Fin 24) : mulCoeff 6 21 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_22 (k : Fin 24) : mulCoeff 6 22 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 2, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_6_23 (k : Fin 24) : mulCoeff 6 23 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_6 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 6 j k : ℂ)*basisEval k) = basisEval 6*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 6 0 k : ℂ)*basisEval k) = basisEval 6*basisEval 0
    simp only [coeff_6_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 6 1 k : ℂ)*basisEval k) = basisEval 6*basisEval 1
    simp only [coeff_6_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 6 2 k : ℂ)*basisEval k) = basisEval 6*basisEval 2
    simp only [coeff_6_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 6 3 k : ℂ)*basisEval k) = basisEval 6*basisEval 3
    simp only [coeff_6_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 6 4 k : ℂ)*basisEval k) = basisEval 6*basisEval 4
    simp only [coeff_6_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 6 5 k : ℂ)*basisEval k) = basisEval 6*basisEval 5
    simp only [coeff_6_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 6 6 k : ℂ)*basisEval k) = basisEval 6*basisEval 6
    simp only [coeff_6_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -(1) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 6 7 k : ℂ)*basisEval k) = basisEval 6*basisEval 7
    simp only [coeff_6_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*1) * sC_sq + -((s : ℂ)) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 6 8 k : ℂ)*basisEval k) = basisEval 6*basisEval 8
    simp only [coeff_6_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 6 9 k : ℂ)*basisEval k) = basisEval 6*basisEval 9
    simp only [coeff_6_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)) * sC_sq + -((s : ℂ)*(x : ℂ)) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 6 10 k : ℂ)*basisEval k) = basisEval 6*basisEval 10
    simp only [coeff_6_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 6 11 k : ℂ)*basisEval k) = basisEval 6*basisEval 11
    simp only [coeff_6_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)^2) * sC_sq + -((s : ℂ)*(x : ℂ)^2) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 6 12 k : ℂ)*basisEval k) = basisEval 6*basisEval 12
    simp only [coeff_6_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 6 13 k : ℂ)*basisEval k) = basisEval 6*basisEval 13
    simp only [coeff_6_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 6 14 k : ℂ)*basisEval k) = basisEval 6*basisEval 14
    simp only [coeff_6_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 6 15 k : ℂ)*basisEval k) = basisEval 6*basisEval 15
    simp only [coeff_6_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 6 16 k : ℂ)*basisEval k) = basisEval 6*basisEval 16
    simp only [coeff_6_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 6 17 k : ℂ)*basisEval k) = basisEval 6*basisEval 17
    simp only [coeff_6_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 6 18 k : ℂ)*basisEval k) = basisEval 6*basisEval 18
    simp only [coeff_6_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -(Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 6 19 k : ℂ)*basisEval k) = basisEval 6*basisEval 19
    simp only [coeff_6_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*Complex.I) * sC_sq + -((s : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 6 20 k : ℂ)*basisEval k) = basisEval 6*basisEval 20
    simp only [coeff_6_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 6 21 k : ℂ)*basisEval k) = basisEval 6*basisEval 21
    simp only [coeff_6_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 6 22 k : ℂ)*basisEval k) = basisEval 6*basisEval 22
    simp only [coeff_6_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 6 23 k : ℂ)*basisEval k) = basisEval 6*basisEval 23
    simp only [coeff_6_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)^2*Complex.I) * uC_sq

end CGLMP5.Scalar
