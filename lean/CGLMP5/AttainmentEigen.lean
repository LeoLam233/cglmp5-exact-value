import CGLMP5.AttainmentRows
import CGLMP5.AttainmentColumn0
import CGLMP5.AttainmentColumn1
import CGLMP5.AttainmentColumn2
import CGLMP5.AttainmentColumn3
import CGLMP5.AttainmentColumn4
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace CGLMP5.Attainment
noncomputable section
open scoped BigOperators Matrix

/-- Every one of125 full-space entries from a diagonal input is accounted for. -/
lemma matrixBell_diagonal_column (i j l : Fin 5) : matrixBell (i,j) (l,l) =
    if i = j then toeplitzEntry i l else 0 := by
  by_cases h : i = j
  · subst j
    simp only [ite_true]
    fin_cases l
    · exact matrixBell_diagonal_0 i
    · exact matrixBell_diagonal_1 i
    · exact matrixBell_diagonal_2 i
    · exact matrixBell_diagonal_3 i
    · exact matrixBell_diagonal_4 i
  · simp [h, matrixBell_off_diagonal i j l h]

/-- The eigen-equation is in all25 coordinates, including every off-diagonal output. -/
lemma rawState_mulVec : matrixBell *ᵥ WithLp.ofLp rawState =
    fun ij => (mu : ℂ) * rawState ij := by
  funext ij
  rcases ij with ⟨i,j⟩
  change (∑ kl : Fin 5 × Fin 5, matrixBell (i,j) kl *
    (if kl.1 = kl.2 then (gamma kl.1 : ℂ) else 0)) =
    (mu : ℂ) * (if i = j then (gamma i : ℂ) else 0)
  rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    matrixBell_diagonal_column]
  by_cases h : i = j
  · simp only [h, ite_true]
    exact toeplitz_gamma j
  · simp [h]

lemma rawState_eigen :
    Matrix.toEuclideanCLM (n := Fin 5 × Fin 5) (𝕜 := ℂ) matrixBell rawState =
      (mu : ℂ) • rawState := by
  apply PiLp.ext
  intro ij
  exact congrFun rawState_mulVec ij

/-- The normalized physical vector satisfies the full25-dimensional Bell eigen-equation. -/
lemma state_eigen :
    Matrix.toEuclideanCLM (n := Fin 5 × Fin 5) (𝕜 := ℂ) matrixBell state =
      (mu : ℂ) • state := by
  rw [state, map_smul, rawState_eigen, smul_comm]

lemma state_inner_self : inner ℂ state state = 1 := by
  rw [inner_self_eq_norm_sq_to_K, state_norm]
  norm_num

lemma state_expectation :
    inner ℂ state (Matrix.toEuclideanCLM (n := Fin 5 × Fin 5) (𝕜 := ℂ) matrixBell state) =
      (mu : ℂ) := by
  rw [state_eigen, inner_smul_right, state_inner_self, mul_one]

end
end CGLMP5.Attainment
