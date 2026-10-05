import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_14_0 (k : Fin 24) : mulCoeff 14 0 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_1 (k : Fin 24) : mulCoeff 14 1 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_2 (k : Fin 24) : mulCoeff 14 2 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_3 (k : Fin 24) : mulCoeff 14 3 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_4 (k : Fin 24) : mulCoeff 14 4 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500, -200, 100, -20, 0, 5, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_5 (k : Fin 24) : mulCoeff 14 5 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_6 (k : Fin 24) : mulCoeff 14 6 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_7 (k : Fin 24) : mulCoeff 14 7 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_8 (k : Fin 24) : mulCoeff 14 8 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_9 (k : Fin 24) : mulCoeff 14 9 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_10 (k : Fin 24) : mulCoeff 14 10 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500, -200, 100, -20, 0, 5] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_11 (k : Fin 24) : mulCoeff 14 11 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_12 (k : Fin 24) : mulCoeff 14 12 k = (![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_13 (k : Fin 24) : mulCoeff 14 13 k = (![0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_14 (k : Fin 24) : mulCoeff 14 14 k = (![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_15 (k : Fin 24) : mulCoeff 14 15 k = (![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_16 (k : Fin 24) : mulCoeff 14 16 k = (![-500, 200, -100, 20, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_17 (k : Fin 24) : mulCoeff 14 17 k = (![1000, -500, 100, -100, -25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_18 (k : Fin 24) : mulCoeff 14 18 k = (![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_19 (k : Fin 24) : mulCoeff 14 19 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_20 (k : Fin 24) : mulCoeff 14 20 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_21 (k : Fin 24) : mulCoeff 14 21 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_22 (k : Fin 24) : mulCoeff 14 22 k = (![0, 0, 0, 0, 0, 0, -500, 200, -100, 20, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_14_23 (k : Fin 24) : mulCoeff 14 23 k = (![0, 0, 0, 0, 0, 0, 1000, -500, 100, -100, -25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_14 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 14 j k : ℂ)*basisEval k) = basisEval 14*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 14 0 k : ℂ)*basisEval k) = basisEval 14*basisEval 0
    simp only [coeff_14_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 14 1 k : ℂ)*basisEval k) = basisEval 14*basisEval 1
    simp only [coeff_14_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 14 2 k : ℂ)*basisEval k) = basisEval 14*basisEval 2
    simp only [coeff_14_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 14 3 k : ℂ)*basisEval k) = basisEval 14*basisEval 3
    simp only [coeff_14_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 14 4 k : ℂ)*basisEval k) = basisEval 14*basisEval 4
    simp only [coeff_14_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -(Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 14 5 k : ℂ)*basisEval k) = basisEval 14*basisEval 5
    simp only [coeff_14_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*Complex.I + (-20)*(x : ℂ)*Complex.I + (5)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 14 6 k : ℂ)*basisEval k) = basisEval 14*basisEval 6
    simp only [coeff_14_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 14 7 k : ℂ)*basisEval k) = basisEval 14*basisEval 7
    simp only [coeff_14_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 14 8 k : ℂ)*basisEval k) = basisEval 14*basisEval 8
    simp only [coeff_14_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 14 9 k : ℂ)*basisEval k) = basisEval 14*basisEval 9
    simp only [coeff_14_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 14 10 k : ℂ)*basisEval k) = basisEval 14*basisEval 10
    simp only [coeff_14_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 14 11 k : ℂ)*basisEval k) = basisEval 14*basisEval 11
    simp only [coeff_14_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*(u : ℂ)*Complex.I + (-20)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 14 12 k : ℂ)*basisEval k) = basisEval 14*basisEval 12
    simp only [coeff_14_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 14 13 k : ℂ)*basisEval k) = basisEval 14*basisEval 13
    simp only [coeff_14_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 14 14 k : ℂ)*basisEval k) = basisEval 14*basisEval 14
    simp only [coeff_14_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 14 15 k : ℂ)*basisEval k) = basisEval 14*basisEval 15
    simp only [coeff_14_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 14 16 k : ℂ)*basisEval k) = basisEval 14*basisEval 16
    simp only [coeff_14_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*1) * xC_cubic + -((x : ℂ)^3) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 14 17 k : ℂ)*basisEval k) = basisEval 14*basisEval 17
    simp only [coeff_14_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((200)*1 + (20)*(x : ℂ) + (-5)*(x : ℂ)^2) * sC_sq + -((-1)*(s : ℂ)) * xC_cubic + -((s : ℂ)*(x : ℂ)^3) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 14 18 k : ℂ)*basisEval k) = basisEval 14*basisEval 18
    simp only [coeff_14_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 14 19 k : ℂ)*basisEval k) = basisEval 14*basisEval 19
    simp only [coeff_14_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 14 20 k : ℂ)*basisEval k) = basisEval 14*basisEval 20
    simp only [coeff_14_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 14 21 k : ℂ)*basisEval k) = basisEval 14*basisEval 21
    simp only [coeff_14_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)^2*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 14 22 k : ℂ)*basisEval k) = basisEval 14*basisEval 22
    simp only [coeff_14_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(u : ℂ)) * xC_cubic + -((x : ℂ)^3*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 14 23 k : ℂ)*basisEval k) = basisEval 14*basisEval 23
    simp only [coeff_14_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((200)*(u : ℂ) + (20)*(x : ℂ)*(u : ℂ) + (-5)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((-1)*(s : ℂ)*(u : ℂ)) * xC_cubic + -((s : ℂ)*(x : ℂ)^3*(u : ℂ)) * Complex.I_sq

end CGLMP5.Scalar
