import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_13_0 (k : Fin 24) : mulCoeff 13 0 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_1 (k : Fin 24) : mulCoeff 13 1 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_2 (k : Fin 24) : mulCoeff 13 2 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_3 (k : Fin 24) : mulCoeff 13 3 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_4 (k : Fin 24) : mulCoeff 13 4 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_5 (k : Fin 24) : mulCoeff 13 5 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_6 (k : Fin 24) : mulCoeff 13 6 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_7 (k : Fin 24) : mulCoeff 13 7 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_8 (k : Fin 24) : mulCoeff 13 8 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_9 (k : Fin 24) : mulCoeff 13 9 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_10 (k : Fin 24) : mulCoeff 13 10 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_11 (k : Fin 24) : mulCoeff 13 11 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_12 (k : Fin 24) : mulCoeff 13 12 k = (![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_13 (k : Fin 24) : mulCoeff 13 13 k = (![-5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_14 (k : Fin 24) : mulCoeff 13 14 k = (![0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_15 (k : Fin 24) : mulCoeff 13 15 k = (![0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_16 (k : Fin 24) : mulCoeff 13 16 k = (![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_17 (k : Fin 24) : mulCoeff 13 17 k = (![0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_18 (k : Fin 24) : mulCoeff 13 18 k = (![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_19 (k : Fin 24) : mulCoeff 13 19 k = (![0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_20 (k : Fin 24) : mulCoeff 13 20 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_21 (k : Fin 24) : mulCoeff 13 21 k = (![0, 0, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_22 (k : Fin 24) : mulCoeff 13 22 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_13_23 (k : Fin 24) : mulCoeff 13 23 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_13 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 13 j k : ℂ)*basisEval k) = basisEval 13*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 13 0 k : ℂ)*basisEval k) = basisEval 13*basisEval 0
    simp only [coeff_13_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 13 1 k : ℂ)*basisEval k) = basisEval 13*basisEval 1
    simp only [coeff_13_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -(Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 13 2 k : ℂ)*basisEval k) = basisEval 13*basisEval 2
    simp only [coeff_13_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 13 3 k : ℂ)*basisEval k) = basisEval 13*basisEval 3
    simp only [coeff_13_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 13 4 k : ℂ)*basisEval k) = basisEval 13*basisEval 4
    simp only [coeff_13_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 13 5 k : ℂ)*basisEval k) = basisEval 13*basisEval 5
    simp only [coeff_13_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 13 6 k : ℂ)*basisEval k) = basisEval 13*basisEval 6
    simp only [coeff_13_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 13 7 k : ℂ)*basisEval k) = basisEval 13*basisEval 7
    simp only [coeff_13_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 13 8 k : ℂ)*basisEval k) = basisEval 13*basisEval 8
    simp only [coeff_13_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 13 9 k : ℂ)*basisEval k) = basisEval 13*basisEval 9
    simp only [coeff_13_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*(u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 13 10 k : ℂ)*basisEval k) = basisEval 13*basisEval 10
    simp only [coeff_13_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 13 11 k : ℂ)*basisEval k) = basisEval 13*basisEval 11
    simp only [coeff_13_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 13 12 k : ℂ)*basisEval k) = basisEval 13*basisEval 12
    simp only [coeff_13_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 13 13 k : ℂ)*basisEval k) = basisEval 13*basisEval 13
    simp only [coeff_13_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*1) * sC_sq + -((s : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 13 14 k : ℂ)*basisEval k) = basisEval 13*basisEval 14
    simp only [coeff_13_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 13 15 k : ℂ)*basisEval k) = basisEval 13*basisEval 15
    simp only [coeff_13_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(x : ℂ)) * sC_sq + -((s : ℂ)^2*(x : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 13 16 k : ℂ)*basisEval k) = basisEval 13*basisEval 16
    simp only [coeff_13_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 13 17 k : ℂ)*basisEval k) = basisEval 13*basisEval 17
    simp only [coeff_13_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(x : ℂ)^2) * sC_sq + -((s : ℂ)^2*(x : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 13 18 k : ℂ)*basisEval k) = basisEval 13*basisEval 18
    simp only [coeff_13_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 13 19 k : ℂ)*basisEval k) = basisEval 13*basisEval 19
    simp only [coeff_13_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(u : ℂ)) * sC_sq + -((s : ℂ)^2*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 13 20 k : ℂ)*basisEval k) = basisEval 13*basisEval 20
    simp only [coeff_13_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 13 21 k : ℂ)*basisEval k) = basisEval 13*basisEval 21
    simp only [coeff_13_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(x : ℂ)*(u : ℂ)) * sC_sq + -((s : ℂ)^2*(x : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 13 22 k : ℂ)*basisEval k) = basisEval 13*basisEval 22
    simp only [coeff_13_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)^2*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 13 23 k : ℂ)*basisEval k) = basisEval 13*basisEval 23
    simp only [coeff_13_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)^2*(x : ℂ)^2*(u : ℂ)) * Complex.I_sq

end CGLMP5.Scalar
