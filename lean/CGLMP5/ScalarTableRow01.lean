import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_1_0 (k : Fin 24) : mulCoeff 1 0 k = (![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_1 (k : Fin 24) : mulCoeff 1 1 k = (![5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_2 (k : Fin 24) : mulCoeff 1 2 k = (![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_3 (k : Fin 24) : mulCoeff 1 3 k = (![0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_4 (k : Fin 24) : mulCoeff 1 4 k = (![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_5 (k : Fin 24) : mulCoeff 1 5 k = (![0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_6 (k : Fin 24) : mulCoeff 1 6 k = (![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_7 (k : Fin 24) : mulCoeff 1 7 k = (![0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_8 (k : Fin 24) : mulCoeff 1 8 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_9 (k : Fin 24) : mulCoeff 1 9 k = (![0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_10 (k : Fin 24) : mulCoeff 1 10 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_11 (k : Fin 24) : mulCoeff 1 11 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_12 (k : Fin 24) : mulCoeff 1 12 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_13 (k : Fin 24) : mulCoeff 1 13 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_14 (k : Fin 24) : mulCoeff 1 14 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_15 (k : Fin 24) : mulCoeff 1 15 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_16 (k : Fin 24) : mulCoeff 1 16 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_17 (k : Fin 24) : mulCoeff 1 17 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_18 (k : Fin 24) : mulCoeff 1 18 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_19 (k : Fin 24) : mulCoeff 1 19 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_20 (k : Fin 24) : mulCoeff 1 20 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_21 (k : Fin 24) : mulCoeff 1 21 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_22 (k : Fin 24) : mulCoeff 1 22 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_1_23 (k : Fin 24) : mulCoeff 1 23 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_1 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 1 j k : ℂ)*basisEval k) = basisEval 1*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 1 0 k : ℂ)*basisEval k) = basisEval 1*basisEval 0
    simp only [coeff_1_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 1 1 k : ℂ)*basisEval k) = basisEval 1*basisEval 1
    simp only [coeff_1_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -(1) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 1 2 k : ℂ)*basisEval k) = basisEval 1*basisEval 2
    simp only [coeff_1_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 1 3 k : ℂ)*basisEval k) = basisEval 1*basisEval 3
    simp only [coeff_1_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 1 4 k : ℂ)*basisEval k) = basisEval 1*basisEval 4
    simp only [coeff_1_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 1 5 k : ℂ)*basisEval k) = basisEval 1*basisEval 5
    simp only [coeff_1_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 1 6 k : ℂ)*basisEval k) = basisEval 1*basisEval 6
    simp only [coeff_1_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 1 7 k : ℂ)*basisEval k) = basisEval 1*basisEval 7
    simp only [coeff_1_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((u : ℂ)) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 1 8 k : ℂ)*basisEval k) = basisEval 1*basisEval 8
    simp only [coeff_1_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 1 9 k : ℂ)*basisEval k) = basisEval 1*basisEval 9
    simp only [coeff_1_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*(u : ℂ)) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 1 10 k : ℂ)*basisEval k) = basisEval 1*basisEval 10
    simp only [coeff_1_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 1 11 k : ℂ)*basisEval k) = basisEval 1*basisEval 11
    simp only [coeff_1_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 1 12 k : ℂ)*basisEval k) = basisEval 1*basisEval 12
    simp only [coeff_1_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 1 13 k : ℂ)*basisEval k) = basisEval 1*basisEval 13
    simp only [coeff_1_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -(Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 1 14 k : ℂ)*basisEval k) = basisEval 1*basisEval 14
    simp only [coeff_1_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 1 15 k : ℂ)*basisEval k) = basisEval 1*basisEval 15
    simp only [coeff_1_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 1 16 k : ℂ)*basisEval k) = basisEval 1*basisEval 16
    simp only [coeff_1_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 1 17 k : ℂ)*basisEval k) = basisEval 1*basisEval 17
    simp only [coeff_1_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 1 18 k : ℂ)*basisEval k) = basisEval 1*basisEval 18
    simp only [coeff_1_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 1 19 k : ℂ)*basisEval k) = basisEval 1*basisEval 19
    simp only [coeff_1_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 1 20 k : ℂ)*basisEval k) = basisEval 1*basisEval 20
    simp only [coeff_1_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 1 21 k : ℂ)*basisEval k) = basisEval 1*basisEval 21
    simp only [coeff_1_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*(u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 1 22 k : ℂ)*basisEval k) = basisEval 1*basisEval 22
    simp only [coeff_1_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 1 23 k : ℂ)*basisEval k) = basisEval 1*basisEval 23
    simp only [coeff_1_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq

end CGLMP5.Scalar
