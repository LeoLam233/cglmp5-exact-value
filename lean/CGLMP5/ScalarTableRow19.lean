import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_19_0 (k : Fin 24) : mulCoeff 19 0 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_1 (k : Fin 24) : mulCoeff 19 1 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_2 (k : Fin 24) : mulCoeff 19 2 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_3 (k : Fin 24) : mulCoeff 19 3 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_4 (k : Fin 24) : mulCoeff 19 4 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_5 (k : Fin 24) : mulCoeff 19 5 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_6 (k : Fin 24) : mulCoeff 19 6 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_7 (k : Fin 24) : mulCoeff 19 7 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_8 (k : Fin 24) : mulCoeff 19 8 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_9 (k : Fin 24) : mulCoeff 19 9 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 10, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_10 (k : Fin 24) : mulCoeff 19 10 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_11 (k : Fin 24) : mulCoeff 19 11 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 10, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_12 (k : Fin 24) : mulCoeff 19 12 k = (![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_13 (k : Fin 24) : mulCoeff 19 13 k = (![0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_14 (k : Fin 24) : mulCoeff 19 14 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_15 (k : Fin 24) : mulCoeff 19 15 k = (![0, 0, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_16 (k : Fin 24) : mulCoeff 19 16 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_17 (k : Fin 24) : mulCoeff 19 17 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_18 (k : Fin 24) : mulCoeff 19 18 k = (![-10, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_19 (k : Fin 24) : mulCoeff 19 19 k = (![-50, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_20 (k : Fin 24) : mulCoeff 19 20 k = (![0, 0, -10, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_21 (k : Fin 24) : mulCoeff 19 21 k = (![0, 0, -50, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_22 (k : Fin 24) : mulCoeff 19 22 k = (![0, 0, 0, 0, -10, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_19_23 (k : Fin 24) : mulCoeff 19 23 k = (![0, 0, 0, 0, -50, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_19 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 19 j k : ℂ)*basisEval k) = basisEval 19*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 19 0 k : ℂ)*basisEval k) = basisEval 19*basisEval 0
    simp only [coeff_19_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 19 1 k : ℂ)*basisEval k) = basisEval 19*basisEval 1
    simp only [coeff_19_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 19 2 k : ℂ)*basisEval k) = basisEval 19*basisEval 2
    simp only [coeff_19_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 19 3 k : ℂ)*basisEval k) = basisEval 19*basisEval 3
    simp only [coeff_19_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*(u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 19 4 k : ℂ)*basisEval k) = basisEval 19*basisEval 4
    simp only [coeff_19_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 19 5 k : ℂ)*basisEval k) = basisEval 19*basisEval 5
    simp only [coeff_19_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 19 6 k : ℂ)*basisEval k) = basisEval 19*basisEval 6
    simp only [coeff_19_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*Complex.I) * sC_sq + -((s : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 19 7 k : ℂ)*basisEval k) = basisEval 19*basisEval 7
    simp only [coeff_19_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*Complex.I + (2)*(s : ℂ)*Complex.I) * sC_sq + -((s : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 19 8 k : ℂ)*basisEval k) = basisEval 19*basisEval 8
    simp only [coeff_19_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 19 9 k : ℂ)*basisEval k) = basisEval 19*basisEval 9
    simp only [coeff_19_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*(x : ℂ)*Complex.I + (2)*(s : ℂ)*(x : ℂ)*Complex.I) * sC_sq + -((s : ℂ)^2*(x : ℂ)*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 19 10 k : ℂ)*basisEval k) = basisEval 19*basisEval 10
    simp only [coeff_19_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 19 11 k : ℂ)*basisEval k) = basisEval 19*basisEval 11
    simp only [coeff_19_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((10)*(x : ℂ)^2*Complex.I + (2)*(s : ℂ)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)^2*(x : ℂ)^2*Complex.I) * uC_sq
  · change (∑ k : Fin 24, (mulCoeff 19 12 k : ℂ)*basisEval k) = basisEval 19*basisEval 12
    simp only [coeff_19_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 19 13 k : ℂ)*basisEval k) = basisEval 19*basisEval 13
    simp only [coeff_19_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(u : ℂ)) * sC_sq + -((s : ℂ)^2*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 19 14 k : ℂ)*basisEval k) = basisEval 19*basisEval 14
    simp only [coeff_19_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 19 15 k : ℂ)*basisEval k) = basisEval 19*basisEval 15
    simp only [coeff_19_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(x : ℂ)*(u : ℂ)) * sC_sq + -((s : ℂ)^2*(x : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 19 16 k : ℂ)*basisEval k) = basisEval 19*basisEval 16
    simp only [coeff_19_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)^2*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 19 17 k : ℂ)*basisEval k) = basisEval 19*basisEval 17
    simp only [coeff_19_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)^2*(x : ℂ)^2*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 19 18 k : ℂ)*basisEval k) = basisEval 19*basisEval 18
    simp only [coeff_19_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-2)*1) * sC_sq + -((-1)*(s : ℂ)) * uC_sq + -((s : ℂ)*(u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 19 19 k : ℂ)*basisEval k) = basisEval 19*basisEval 19
    simp only [coeff_19_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-10)*1 + (-2)*(s : ℂ)) * sC_sq + -((-1)*(s : ℂ)^2) * uC_sq + -((s : ℂ)^2*(u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 19 20 k : ℂ)*basisEval k) = basisEval 19*basisEval 20
    simp only [coeff_19_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-2)*(x : ℂ)) * sC_sq + -((-1)*(s : ℂ)*(x : ℂ)) * uC_sq + -((s : ℂ)*(x : ℂ)*(u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 19 21 k : ℂ)*basisEval k) = basisEval 19*basisEval 21
    simp only [coeff_19_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-10)*(x : ℂ) + (-2)*(s : ℂ)*(x : ℂ)) * sC_sq + -((-1)*(s : ℂ)^2*(x : ℂ)) * uC_sq + -((s : ℂ)^2*(x : ℂ)*(u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 19 22 k : ℂ)*basisEval k) = basisEval 19*basisEval 22
    simp only [coeff_19_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-2)*(x : ℂ)^2) * sC_sq + -((-1)*(s : ℂ)*(x : ℂ)^2) * uC_sq + -((s : ℂ)*(x : ℂ)^2*(u : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 19 23 k : ℂ)*basisEval k) = basisEval 19*basisEval 23
    simp only [coeff_19_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-10)*(x : ℂ)^2 + (-2)*(s : ℂ)*(x : ℂ)^2) * sC_sq + -((-1)*(s : ℂ)^2*(x : ℂ)^2) * uC_sq + -((s : ℂ)^2*(x : ℂ)^2*(u : ℂ)^2) * Complex.I_sq

end CGLMP5.Scalar
