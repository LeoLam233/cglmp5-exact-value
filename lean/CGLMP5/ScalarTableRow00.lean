import CGLMP5.ScalarProductsBase
import Mathlib.Tactic.LinearCombination

namespace CGLMP5.Scalar

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private lemma coeff_0_0 (k : Fin 24) : mulCoeff 0 0 k = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_1 (k : Fin 24) : mulCoeff 0 1 k = (![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_2 (k : Fin 24) : mulCoeff 0 2 k = (![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_3 (k : Fin 24) : mulCoeff 0 3 k = (![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_4 (k : Fin 24) : mulCoeff 0 4 k = (![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_5 (k : Fin 24) : mulCoeff 0 5 k = (![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_6 (k : Fin 24) : mulCoeff 0 6 k = (![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_7 (k : Fin 24) : mulCoeff 0 7 k = (![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_8 (k : Fin 24) : mulCoeff 0 8 k = (![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_9 (k : Fin 24) : mulCoeff 0 9 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_10 (k : Fin 24) : mulCoeff 0 10 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_11 (k : Fin 24) : mulCoeff 0 11 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_12 (k : Fin 24) : mulCoeff 0 12 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_13 (k : Fin 24) : mulCoeff 0 13 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_14 (k : Fin 24) : mulCoeff 0 14 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_15 (k : Fin 24) : mulCoeff 0 15 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_16 (k : Fin 24) : mulCoeff 0 16 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_17 (k : Fin 24) : mulCoeff 0 17 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_18 (k : Fin 24) : mulCoeff 0 18 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_19 (k : Fin 24) : mulCoeff 0 19 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_20 (k : Fin 24) : mulCoeff 0 20 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_21 (k : Fin 24) : mulCoeff 0 21 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_22 (k : Fin 24) : mulCoeff 0 22 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

private lemma coeff_0_23 (k : Fin 24) : mulCoeff 0 23 k = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 24 → ℤ) k := by
  fin_cases k <;> decide +kernel

lemma mulCoeff_sound_row_0 (j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff 0 j k : ℂ)*basisEval k) = basisEval 0*basisEval j := by
  fin_cases j
  · change (∑ k : Fin 24, (mulCoeff 0 0 k : ℂ)*basisEval k) = basisEval 0*basisEval 0
    simp only [coeff_0_0]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 1 k : ℂ)*basisEval k) = basisEval 0*basisEval 1
    simp only [coeff_0_1]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 2 k : ℂ)*basisEval k) = basisEval 0*basisEval 2
    simp only [coeff_0_2]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 3 k : ℂ)*basisEval k) = basisEval 0*basisEval 3
    simp only [coeff_0_3]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 4 k : ℂ)*basisEval k) = basisEval 0*basisEval 4
    simp only [coeff_0_4]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 5 k : ℂ)*basisEval k) = basisEval 0*basisEval 5
    simp only [coeff_0_5]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 6 k : ℂ)*basisEval k) = basisEval 0*basisEval 6
    simp only [coeff_0_6]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 7 k : ℂ)*basisEval k) = basisEval 0*basisEval 7
    simp only [coeff_0_7]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 8 k : ℂ)*basisEval k) = basisEval 0*basisEval 8
    simp only [coeff_0_8]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 9 k : ℂ)*basisEval k) = basisEval 0*basisEval 9
    simp only [coeff_0_9]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 10 k : ℂ)*basisEval k) = basisEval 0*basisEval 10
    simp only [coeff_0_10]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 11 k : ℂ)*basisEval k) = basisEval 0*basisEval 11
    simp only [coeff_0_11]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 12 k : ℂ)*basisEval k) = basisEval 0*basisEval 12
    simp only [coeff_0_12]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 13 k : ℂ)*basisEval k) = basisEval 0*basisEval 13
    simp only [coeff_0_13]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 14 k : ℂ)*basisEval k) = basisEval 0*basisEval 14
    simp only [coeff_0_14]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 15 k : ℂ)*basisEval k) = basisEval 0*basisEval 15
    simp only [coeff_0_15]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 16 k : ℂ)*basisEval k) = basisEval 0*basisEval 16
    simp only [coeff_0_16]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 17 k : ℂ)*basisEval k) = basisEval 0*basisEval 17
    simp only [coeff_0_17]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 18 k : ℂ)*basisEval k) = basisEval 0*basisEval 18
    simp only [coeff_0_18]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 19 k : ℂ)*basisEval k) = basisEval 0*basisEval 19
    simp only [coeff_0_19]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 20 k : ℂ)*basisEval k) = basisEval 0*basisEval 20
    simp only [coeff_0_20]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 21 k : ℂ)*basisEval k) = basisEval 0*basisEval 21
    simp only [coeff_0_21]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 22 k : ℂ)*basisEval k) = basisEval 0*basisEval 22
    simp only [coeff_0_22]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring
  · change (∑ k : Fin 24, (mulCoeff 0 23 k : ℂ)*basisEval k) = basisEval 0*basisEval 23
    simp only [coeff_0_23]
    norm_num [basisEval, Fin.sum_univ_succ]
    <;> ring

end CGLMP5.Scalar
