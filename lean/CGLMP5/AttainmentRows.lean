import CGLMP5.AttainmentState
import CGLMP5.AttainmentBellDefs

namespace CGLMP5.Attainment
noncomputable section
open scoped BigOperators Matrix

lemma toeplitz_gamma (i : Fin 5) :
    (∑ j : Fin 5, toeplitzEntry i j * (gamma j : ℂ)) = (mu : ℂ) * (gamma i : ℂ) := by
  have h0 := congrArg (fun t : ℝ => (t : ℂ))
    (row_zero mu s u s_sq u_sq mu_cubic)
  have h1 := congrArg (fun t : ℝ => (t : ℂ))
    (row_one mu s u s_sq u_sq mu_cubic)
  have h2 := congrArg (fun t : ℝ => (t : ℂ))
    (row_two mu s u s_sq u_sq mu_cubic)
  simp only [f1, f2, f3, f4] at h0 h1 h2
  push_cast at h0 h1 h2
  fin_cases i <;>
    norm_num [toeplitzEntry, distanceIndex, gamma, Fin.sum_univ_succ, schmidtA, schmidtB]
  all_goals first
    | linear_combination -h0
    | linear_combination -h1
    | linear_combination -h2

end
end CGLMP5.Attainment
