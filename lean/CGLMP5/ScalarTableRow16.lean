import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_16_0 (k : Fin 24) : mulCoeff 16 0 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_1 (k : Fin 24) : mulCoeff 16 1 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_2 (k : Fin 24) : mulCoeff 16 2 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500, -200, 100, -20, 0, 5, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_3 (k : Fin 24) : mulCoeff 16 3 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_4 (k : Fin 24) : mulCoeff 16 4 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5000, 2500, 0, 300, 225, -20, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_5 (k : Fin 24) : mulCoeff 16 5 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12500, -5000, 1500, 0, -100, 225, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_6 (k : Fin 24) : mulCoeff 16 6 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_7 (k : Fin 24) : mulCoeff 16 7 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_8 (k : Fin 24) : mulCoeff 16 8 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500, -200, 100, -20, 0, 5] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_9 (k : Fin 24) : mulCoeff 16 9 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_10 (k : Fin 24) : mulCoeff 16 10 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5000, 2500, 0, 300, 225, -20] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_11 (k : Fin 24) : mulCoeff 16 11 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12500, -5000, 1500, 0, -100, 225] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_12 (k : Fin 24) : mulCoeff 16 12 k = (![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_13 (k : Fin 24) : mulCoeff 16 13 k = (![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_14 (k : Fin 24) : mulCoeff 16 14 k = (![-500, 200, -100, 20, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_15 (k : Fin 24) : mulCoeff 16 15 k = (![1000, -500, 100, -100, -25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_16 (k : Fin 24) : mulCoeff 16 16 k = (![5000, -2500, 0, -300, -225, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_17 (k : Fin 24) : mulCoeff 16 17 k = (![-12500, 5000, -1500, 0, 100, -225, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_18 (k : Fin 24) : mulCoeff 16 18 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_19 (k : Fin 24) : mulCoeff 16 19 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_20 (k : Fin 24) : mulCoeff 16 20 k = (![0, 0, 0, 0, 0, 0, -500, 200, -100, 20, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_21 (k : Fin 24) : mulCoeff 16 21 k = (![0, 0, 0, 0, 0, 0, 1000, -500, 100, -100, -25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_22 (k : Fin 24) : mulCoeff 16 22 k = (![0, 0, 0, 0, 0, 0, 5000, -2500, 0, -300, -225, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_16_23 (k : Fin 24) : mulCoeff 16 23 k = (![0, 0, 0, 0, 0, 0, -12500, 5000, -1500, 0, 100, -225, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_16 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 16 j k : ℂ)*basisEval k) = basisEval 16*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 16 0 k : ℂ)*basisEval k) = basisEval 16*basisEval 0
    simp only [coeff_16_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 16 1 k : ℂ)*basisEval k) = basisEval 16*basisEval 1
    simp only [coeff_16_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 16 2 k : ℂ)*basisEval k) = basisEval 16*basisEval 2
    simp only [coeff_16_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -(Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 16 3 k : ℂ)*basisEval k) = basisEval 16*basisEval 3
    simp only [coeff_16_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*Complex.I + (-20)*(x : ℂ)*Complex.I + (5)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 16 4 k : ℂ)*basisEval k) = basisEval 16*basisEval 4
    simp only [coeff_16_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1000)*Complex.I + (-100)*(x : ℂ)*Complex.I + (25)*(x : ℂ)^2*Complex.I) * sC_sq + -((x : ℂ)*Complex.I + (5)*(s : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 16 5 k : ℂ)*basisEval k) = basisEval 16*basisEval 5
    simp only [coeff_16_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2500)*Complex.I + (300)*(x : ℂ)*Complex.I + (-20)*(x : ℂ)^2*Complex.I + (-1000)*(s : ℂ)*Complex.I + (-100)*(s : ℂ)*(x : ℂ)*Complex.I + (25)*(s : ℂ)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)*Complex.I + (5)*(s : ℂ)^2*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 16 6 k : ℂ)*basisEval k) = basisEval 16*basisEval 6
    simp only [coeff_16_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 16 7 k : ℂ)*basisEval k) = basisEval 16*basisEval 7
    simp only [coeff_16_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 16 8 k : ℂ)*basisEval k) = basisEval 16*basisEval 8
    simp only [coeff_16_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 16 9 k : ℂ)*basisEval k) = basisEval 16*basisEval 9
    simp only [coeff_16_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*(u : ℂ)*Complex.I + (-20)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 16 10 k : ℂ)*basisEval k) = basisEval 16*basisEval 10
    simp only [coeff_16_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1000)*(u : ℂ)*Complex.I + (-100)*(x : ℂ)*(u : ℂ)*Complex.I + (25)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((x : ℂ)*(u : ℂ)*Complex.I + (5)*(s : ℂ)*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 16 11 k : ℂ)*basisEval k) = basisEval 16*basisEval 11
    simp only [coeff_16_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((2500)*(u : ℂ)*Complex.I + (300)*(x : ℂ)*(u : ℂ)*Complex.I + (-20)*(x : ℂ)^2*(u : ℂ)*Complex.I + (-1000)*(s : ℂ)*(u : ℂ)*Complex.I + (-100)*(s : ℂ)*(x : ℂ)*(u : ℂ)*Complex.I + (25)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(s : ℂ)^2*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 16 12 k : ℂ)*basisEval k) = basisEval 16*basisEval 12
    simp only [coeff_16_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 16 13 k : ℂ)*basisEval k) = basisEval 16*basisEval 13
    simp only [coeff_16_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)^2) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 16 14 k : ℂ)*basisEval k) = basisEval 16*basisEval 14
    simp only [coeff_16_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*1) * xC_cubic + -((x : ℂ)^3) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 16 15 k : ℂ)*basisEval k) = basisEval 16*basisEval 15
    simp only [coeff_16_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((200)*1 + (20)*(x : ℂ) + (-5)*(x : ℂ)^2) * sC_sq + -((-1)*(s : ℂ)) * xC_cubic + -((s : ℂ)*(x : ℂ)^3) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 16 16 k : ℂ)*basisEval k) = basisEval 16*basisEval 16
    simp only [coeff_16_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((1000)*1 + (100)*(x : ℂ) + (-25)*(x : ℂ)^2) * sC_sq + -((-1)*(x : ℂ) + (-5)*(s : ℂ)) * xC_cubic + -((x : ℂ)^4) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 16 17 k : ℂ)*basisEval k) = basisEval 16*basisEval 17
    simp only [coeff_16_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-2500)*1 + (-300)*(x : ℂ) + (20)*(x : ℂ)^2 + (1000)*(s : ℂ) + (100)*(s : ℂ)*(x : ℂ) + (-25)*(s : ℂ)*(x : ℂ)^2) * sC_sq + -((-1)*(s : ℂ)*(x : ℂ) + (-5)*(s : ℂ)^2) * xC_cubic + -((s : ℂ)*(x : ℂ)^4) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 16 18 k : ℂ)*basisEval k) = basisEval 16*basisEval 18
    simp only [coeff_16_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 16 19 k : ℂ)*basisEval k) = basisEval 16*basisEval 19
    simp only [coeff_16_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((s : ℂ)*(x : ℂ)^2*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 16 20 k : ℂ)*basisEval k) = basisEval 16*basisEval 20
    simp only [coeff_16_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-1)*(u : ℂ)) * xC_cubic + -((x : ℂ)^3*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 16 21 k : ℂ)*basisEval k) = basisEval 16*basisEval 21
    simp only [coeff_16_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((200)*(u : ℂ) + (20)*(x : ℂ)*(u : ℂ) + (-5)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((-1)*(s : ℂ)*(u : ℂ)) * xC_cubic + -((s : ℂ)*(x : ℂ)^3*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 16 22 k : ℂ)*basisEval k) = basisEval 16*basisEval 22
    simp only [coeff_16_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((1000)*(u : ℂ) + (100)*(x : ℂ)*(u : ℂ) + (-25)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((-1)*(x : ℂ)*(u : ℂ) + (-5)*(s : ℂ)*(u : ℂ)) * xC_cubic + -((x : ℂ)^4*(u : ℂ)) * Complex.I_sq
  · change (∑ k : Fin 24, (mulCoeff 16 23 k : ℂ)*basisEval k) = basisEval 16*basisEval 23
    simp only [coeff_16_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-2500)*(u : ℂ) + (-300)*(x : ℂ)*(u : ℂ) + (20)*(x : ℂ)^2*(u : ℂ) + (1000)*(s : ℂ)*(u : ℂ) + (100)*(s : ℂ)*(x : ℂ)*(u : ℂ) + (-25)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((-1)*(s : ℂ)*(x : ℂ)*(u : ℂ) + (-5)*(s : ℂ)^2*(u : ℂ)) * xC_cubic + -((s : ℂ)*(x : ℂ)^4*(u : ℂ)) * Complex.I_sq

end CGLMP5.Scalar
