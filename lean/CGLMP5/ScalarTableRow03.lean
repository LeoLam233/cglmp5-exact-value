import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_3_0 (k : Fin 24) : mulCoeff 3 0 k = (![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_1 (k : Fin 24) : mulCoeff 3 1 k = (![0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_2 (k : Fin 24) : mulCoeff 3 2 k = (![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_3 (k : Fin 24) : mulCoeff 3 3 k = (![0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_4 (k : Fin 24) : mulCoeff 3 4 k = (![-1000, 500, -100, 100, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_5 (k : Fin 24) : mulCoeff 3 5 k = (![2500, -1000, 500, -100, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_6 (k : Fin 24) : mulCoeff 3 6 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_7 (k : Fin 24) : mulCoeff 3 7 k = (![0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_8 (k : Fin 24) : mulCoeff 3 8 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_9 (k : Fin 24) : mulCoeff 3 9 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_10 (k : Fin 24) : mulCoeff 3 10 k = (![0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_11 (k : Fin 24) : mulCoeff 3 11 k = (![0, 0, 0, 0, 0, 0, 2500, -1000, 500, -100, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_12 (k : Fin 24) : mulCoeff 3 12 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_13 (k : Fin 24) : mulCoeff 3 13 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_14 (k : Fin 24) : mulCoeff 3 14 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_15 (k : Fin 24) : mulCoeff 3 15 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_16 (k : Fin 24) : mulCoeff 3 16 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_17 (k : Fin 24) : mulCoeff 3 17 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2500, -1000, 500, -100, 0, 25, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_18 (k : Fin 24) : mulCoeff 3 18 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_19 (k : Fin 24) : mulCoeff 3 19 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_20 (k : Fin 24) : mulCoeff 3 20 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_21 (k : Fin 24) : mulCoeff 3 21 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_22 (k : Fin 24) : mulCoeff 3 22 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000, 500, -100, 100, 25, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_3_23 (k : Fin 24) : mulCoeff 3 23 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2500, -1000, 500, -100, 0, 25] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_3 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 3 j k : ℂ)*basisEval k) = basisEval 3*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 3 0 k : ℂ)*basisEval k) = basisEval 3*basisEval 0
    simp only [coeff_3_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 3 1 k : ℂ)*basisEval k) = basisEval 3*basisEval 1
    simp only [coeff_3_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 3 2 k : ℂ)*basisEval k) = basisEval 3*basisEval 2
    simp only [coeff_3_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 3 3 k : ℂ)*basisEval k) = basisEval 3*basisEval 3
    simp only [coeff_3_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 3 4 k : ℂ)*basisEval k) = basisEval 3*basisEval 4
    simp only [coeff_3_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*1 + (-20)*(x : ℂ) + (5)*(x : ℂ)^2) * sC_sq + -((s : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 3 5 k : ℂ)*basisEval k) = basisEval 3*basisEval 5
    simp only [coeff_3_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((500)*1 + (100)*(x : ℂ) + (-200)*(s : ℂ) + (-20)*(s : ℂ)*(x : ℂ) + (5)*(s : ℂ)*(x : ℂ)^2) * sC_sq + -((s : ℂ)^2) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 3 6 k : ℂ)*basisEval k) = basisEval 3*basisEval 6
    simp only [coeff_3_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 3 7 k : ℂ)*basisEval k) = basisEval 3*basisEval 7
    simp only [coeff_3_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*(u : ℂ)) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 3 8 k : ℂ)*basisEval k) = basisEval 3*basisEval 8
    simp only [coeff_3_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 3 9 k : ℂ)*basisEval k) = basisEval 3*basisEval 9
    simp only [coeff_3_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 3 10 k : ℂ)*basisEval k) = basisEval 3*basisEval 10
    simp only [coeff_3_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*(u : ℂ) + (-20)*(x : ℂ)*(u : ℂ) + (5)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 3 11 k : ℂ)*basisEval k) = basisEval 3*basisEval 11
    simp only [coeff_3_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((500)*(u : ℂ) + (100)*(x : ℂ)*(u : ℂ) + (-200)*(s : ℂ)*(u : ℂ) + (-20)*(s : ℂ)*(x : ℂ)*(u : ℂ) + (5)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)) * sC_sq + -((s : ℂ)^2*(u : ℂ)) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 3 12 k : ℂ)*basisEval k) = basisEval 3*basisEval 12
    simp only [coeff_3_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 3 13 k : ℂ)*basisEval k) = basisEval 3*basisEval 13
    simp only [coeff_3_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 3 14 k : ℂ)*basisEval k) = basisEval 3*basisEval 14
    simp only [coeff_3_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 3 15 k : ℂ)*basisEval k) = basisEval 3*basisEval 15
    simp only [coeff_3_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 3 16 k : ℂ)*basisEval k) = basisEval 3*basisEval 16
    simp only [coeff_3_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*Complex.I + (-20)*(x : ℂ)*Complex.I + (5)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 3 17 k : ℂ)*basisEval k) = basisEval 3*basisEval 17
    simp only [coeff_3_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((500)*Complex.I + (100)*(x : ℂ)*Complex.I + (-200)*(s : ℂ)*Complex.I + (-20)*(s : ℂ)*(x : ℂ)*Complex.I + (5)*(s : ℂ)*(x : ℂ)^2*Complex.I) * sC_sq + -((s : ℂ)^2*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 3 18 k : ℂ)*basisEval k) = basisEval 3*basisEval 18
    simp only [coeff_3_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 3 19 k : ℂ)*basisEval k) = basisEval 3*basisEval 19
    simp only [coeff_3_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)*(u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 3 20 k : ℂ)*basisEval k) = basisEval 3*basisEval 20
    simp only [coeff_3_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 3 21 k : ℂ)*basisEval k) = basisEval 3*basisEval 21
    simp only [coeff_3_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq
  · change (∑ k : Fin 24, (mulCoeff 3 22 k : ℂ)*basisEval k) = basisEval 3*basisEval 22
    simp only [coeff_3_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((-200)*(u : ℂ)*Complex.I + (-20)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)*(u : ℂ)*Complex.I) * xC_cubic
  · change (∑ k : Fin 24, (mulCoeff 3 23 k : ℂ)*basisEval k) = basisEval 3*basisEval 23
    simp only [coeff_3_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> linear_combination -((500)*(u : ℂ)*Complex.I + (100)*(x : ℂ)*(u : ℂ)*Complex.I + (-200)*(s : ℂ)*(u : ℂ)*Complex.I + (-20)*(s : ℂ)*(x : ℂ)*(u : ℂ)*Complex.I + (5)*(s : ℂ)*(x : ℂ)^2*(u : ℂ)*Complex.I) * sC_sq + -((s : ℂ)^2*(u : ℂ)*Complex.I) * xC_cubic

end CGLMP5.Scalar
