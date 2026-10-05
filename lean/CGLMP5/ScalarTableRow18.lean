import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_18_0 (k : Fin 24) : mulCoeff 18 0 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_1 (k : Fin 24) : mulCoeff 18 1 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_2 (k : Fin 24) : mulCoeff 18 2 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_3 (k : Fin 24) : mulCoeff 18 3 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_4 (k : Fin 24) : mulCoeff 18 4 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_5 (k : Fin 24) : mulCoeff 18 5 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_6 (k : Fin 24) : mulCoeff 18 6 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_7 (k : Fin 24) : mulCoeff 18 7 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_8 (k : Fin 24) : mulCoeff 18 8 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_9 (k : Fin 24) : mulCoeff 18 9 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_10 (k : Fin 24) : mulCoeff 18 10 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 2, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_11 (k : Fin 24) : mulCoeff 18 11 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_12 (k : Fin 24) : mulCoeff 18 12 k = (![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_13 (k : Fin 24) : mulCoeff 18 13 k = (![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_14 (k : Fin 24) : mulCoeff 18 14 k = (![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_15 (k : Fin 24) : mulCoeff 18 15 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_16 (k : Fin 24) : mulCoeff 18 16 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_17 (k : Fin 24) : mulCoeff 18 17 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_18 (k : Fin 24) : mulCoeff 18 18 k = (![-10, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_19 (k : Fin 24) : mulCoeff 18 19 k = (![-10, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_20 (k : Fin 24) : mulCoeff 18 20 k = (![0, 0, -10, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_21 (k : Fin 24) : mulCoeff 18 21 k = (![0, 0, -10, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_22 (k : Fin 24) : mulCoeff 18 22 k = (![0, 0, 0, 0, -10, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_18_23 (k : Fin 24) : mulCoeff 18 23 k = (![0, 0, 0, 0, -10, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_18 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 18 j k : ℂ)*basisEval k) = basisEval 18*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 18 0 k : ℂ)*basisEval k) = basisEval 18*basisEval 0
    simp only [coeff_18_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 18 1 k : ℂ)*basisEval k) = basisEval 18*basisEval 1
    simp only [coeff_18_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 18 2 k : ℂ)*basisEval k) = basisEval 18*basisEval 2
    simp only [coeff_18_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 18 3 k : ℂ)*basisEval k) = basisEval 18*basisEval 3
    simp only [coeff_18_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 18 4 k : ℂ)*basisEval k) = basisEval 18*basisEval 4
    simp only [coeff_18_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 18 5 k : ℂ)*basisEval k) = basisEval 18*basisEval 5
    simp only [coeff_18_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 18 6 k : ℂ)*basisEval k) = basisEval 18*basisEval 6
    simp only [coeff_18_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -(Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 18 7 k : ℂ)*basisEval k) = basisEval 18*basisEval 7
    simp only [coeff_18_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*Complex.I) * sC_sq + -((s : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 18 8 k : ℂ)*basisEval k) = basisEval 18*basisEval 8
    simp only [coeff_18_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 18 9 k : ℂ)*basisEval k) = basisEval 18*basisEval 9
    simp only [coeff_18_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 18 10 k : ℂ)*basisEval k) = basisEval 18*basisEval 10
    simp only [coeff_18_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 18 11 k : ℂ)*basisEval k) = basisEval 18*basisEval 11
    simp only [coeff_18_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 18 12 k : ℂ)*basisEval k) = basisEval 18*basisEval 12
    simp only [coeff_18_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 18 13 k : ℂ)*basisEval k) = basisEval 18*basisEval 13
    simp only [coeff_18_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 18 14 k : ℂ)*basisEval k) = basisEval 18*basisEval 14
    simp only [coeff_18_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 18 15 k : ℂ)*basisEval k) = basisEval 18*basisEval 15
    simp only [coeff_18_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 18 16 k : ℂ)*basisEval k) = basisEval 18*basisEval 16
    simp only [coeff_18_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 18 17 k : ℂ)*basisEval k) = basisEval 18*basisEval 17
    simp only [coeff_18_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)^2*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 18 18 k : ℂ)*basisEval k) = basisEval 18*basisEval 18
    simp only [coeff_18_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*1) * uC_sq + -((u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 18 19 k : ℂ)*basisEval k) = basisEval 18*basisEval 19
    simp only [coeff_18_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-2)*1) * sC_sq + -((-1)*(s : ℂ)) * uC_sq + -((s : ℂ)*(u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 18 20 k : ℂ)*basisEval k) = basisEval 18*basisEval 20
    simp only [coeff_18_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(x : ℂ)) * uC_sq + -((x : ℂ)*(u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 18 21 k : ℂ)*basisEval k) = basisEval 18*basisEval 21
    simp only [coeff_18_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-2)*(x : ℂ)) * sC_sq + -((-1)*(s : ℂ)*(x : ℂ)) * uC_sq + -((s : ℂ)*(x : ℂ)*(u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 18 22 k : ℂ)*basisEval k) = basisEval 18*basisEval 22
    simp only [coeff_18_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(x : ℂ)^2) * uC_sq + -((x : ℂ)^2*(u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 18 23 k : ℂ)*basisEval k) = basisEval 18*basisEval 23
    simp only [coeff_18_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-2)*(x : ℂ)^2) * sC_sq + -((-1)*(s : ℂ)*(x : ℂ)^2) * uC_sq + -((s : ℂ)*(x : ℂ)^2*(u : ℂ)^2) * Complex.I_sq

end CGLMP5.Scalar
