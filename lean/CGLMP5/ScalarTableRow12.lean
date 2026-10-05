import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_12_0 (k : Fin 24) : mulCoeff 12 0 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_1 (k : Fin 24) : mulCoeff 12 1 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_2 (k : Fin 24) : mulCoeff 12 2 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_3 (k : Fin 24) : mulCoeff 12 3 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_4 (k : Fin 24) : mulCoeff 12 4 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_5 (k : Fin 24) : mulCoeff 12 5 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_6 (k : Fin 24) : mulCoeff 12 6 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_7 (k : Fin 24) : mulCoeff 12 7 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_8 (k : Fin 24) : mulCoeff 12 8 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_9 (k : Fin 24) : mulCoeff 12 9 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_10 (k : Fin 24) : mulCoeff 12 10 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_11 (k : Fin 24) : mulCoeff 12 11 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_12 (k : Fin 24) : mulCoeff 12 12 k = (![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_13 (k : Fin 24) : mulCoeff 12 13 k = (![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_14 (k : Fin 24) : mulCoeff 12 14 k = (![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_15 (k : Fin 24) : mulCoeff 12 15 k = (![0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_16 (k : Fin 24) : mulCoeff 12 16 k = (![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_17 (k : Fin 24) : mulCoeff 12 17 k = (![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_18 (k : Fin 24) : mulCoeff 12 18 k = (![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_19 (k : Fin 24) : mulCoeff 12 19 k = (![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_20 (k : Fin 24) : mulCoeff 12 20 k = (![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_21 (k : Fin 24) : mulCoeff 12 21 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_22 (k : Fin 24) : mulCoeff 12 22 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_12_23 (k : Fin 24) : mulCoeff 12 23 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_12 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 12 j k : ℂ)*basisEval k) = basisEval 12*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 12 0 k : ℂ)*basisEval k) = basisEval 12*basisEval 0
    simp only [coeff_12_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 12 1 k : ℂ)*basisEval k) = basisEval 12*basisEval 1
    simp only [coeff_12_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 12 2 k : ℂ)*basisEval k) = basisEval 12*basisEval 2
    simp only [coeff_12_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 12 3 k : ℂ)*basisEval k) = basisEval 12*basisEval 3
    simp only [coeff_12_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 12 4 k : ℂ)*basisEval k) = basisEval 12*basisEval 4
    simp only [coeff_12_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 12 5 k : ℂ)*basisEval k) = basisEval 12*basisEval 5
    simp only [coeff_12_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 12 6 k : ℂ)*basisEval k) = basisEval 12*basisEval 6
    simp only [coeff_12_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 12 7 k : ℂ)*basisEval k) = basisEval 12*basisEval 7
    simp only [coeff_12_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 12 8 k : ℂ)*basisEval k) = basisEval 12*basisEval 8
    simp only [coeff_12_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 12 9 k : ℂ)*basisEval k) = basisEval 12*basisEval 9
    simp only [coeff_12_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 12 10 k : ℂ)*basisEval k) = basisEval 12*basisEval 10
    simp only [coeff_12_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 12 11 k : ℂ)*basisEval k) = basisEval 12*basisEval 11
    simp only [coeff_12_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 12 12 k : ℂ)*basisEval k) = basisEval 12*basisEval 12
    simp only [coeff_12_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -(1) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 12 13 k : ℂ)*basisEval k) = basisEval 12*basisEval 13
    simp only [coeff_12_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 12 14 k : ℂ)*basisEval k) = basisEval 12*basisEval 14
    simp only [coeff_12_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 12 15 k : ℂ)*basisEval k) = basisEval 12*basisEval 15
    simp only [coeff_12_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 12 16 k : ℂ)*basisEval k) = basisEval 12*basisEval 16
    simp only [coeff_12_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 12 17 k : ℂ)*basisEval k) = basisEval 12*basisEval 17
    simp only [coeff_12_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 12 18 k : ℂ)*basisEval k) = basisEval 12*basisEval 18
    simp only [coeff_12_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 12 19 k : ℂ)*basisEval k) = basisEval 12*basisEval 19
    simp only [coeff_12_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 12 20 k : ℂ)*basisEval k) = basisEval 12*basisEval 20
    simp only [coeff_12_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 12 21 k : ℂ)*basisEval k) = basisEval 12*basisEval 21
    simp only [coeff_12_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 12 22 k : ℂ)*basisEval k) = basisEval 12*basisEval 22
    simp only [coeff_12_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 12 23 k : ℂ)*basisEval k) = basisEval 12*basisEval 23
    simp only [coeff_12_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)^2*(u : ℂ)) * Complex.I_sq

end CGLMP5.Scalar
