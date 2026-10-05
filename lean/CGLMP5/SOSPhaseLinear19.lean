import CGLMP5.SOSPhaseLinearData
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Exact sparse phase 19, coordinate 0; valid for every integer numerator vector. -/
theorem phase_linear_19_0 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 0 = (10 : ℤ) * n 6 + (10 : ℤ) * n 7 + (-1 : ℤ) * n 12 + (5 : ℤ) * n 13 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_0]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 1; valid for every integer numerator vector. -/
theorem phase_linear_19_1 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 1 = (2 : ℤ) * n 6 + (10 : ℤ) * n 7 + (1 : ℤ) * n 12 + (-1 : ℤ) * n 13 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_1]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 2; valid for every integer numerator vector. -/
theorem phase_linear_19_2 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 2 = (10 : ℤ) * n 8 + (10 : ℤ) * n 9 + (-1 : ℤ) * n 14 + (5 : ℤ) * n 15 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_2]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 3; valid for every integer numerator vector. -/
theorem phase_linear_19_3 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 3 = (2 : ℤ) * n 8 + (10 : ℤ) * n 9 + (1 : ℤ) * n 14 + (-1 : ℤ) * n 15 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_3]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 4; valid for every integer numerator vector. -/
theorem phase_linear_19_4 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 4 = (10 : ℤ) * n 10 + (10 : ℤ) * n 11 + (-1 : ℤ) * n 16 + (5 : ℤ) * n 17 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_4]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 5; valid for every integer numerator vector. -/
theorem phase_linear_19_5 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 5 = (2 : ℤ) * n 10 + (10 : ℤ) * n 11 + (1 : ℤ) * n 16 + (-1 : ℤ) * n 17 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_5]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 6; valid for every integer numerator vector. -/
theorem phase_linear_19_6 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 6 = (1 : ℤ) * n 0 + (-1 : ℤ) * n 18 + (5 : ℤ) * n 19 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_6]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 7; valid for every integer numerator vector. -/
theorem phase_linear_19_7 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 7 = (1 : ℤ) * n 1 + (1 : ℤ) * n 18 + (-1 : ℤ) * n 19 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_7]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 8; valid for every integer numerator vector. -/
theorem phase_linear_19_8 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 8 = (1 : ℤ) * n 2 + (-1 : ℤ) * n 20 + (5 : ℤ) * n 21 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_8]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 9; valid for every integer numerator vector. -/
theorem phase_linear_19_9 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 9 = (1 : ℤ) * n 3 + (1 : ℤ) * n 20 + (-1 : ℤ) * n 21 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_9]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 10; valid for every integer numerator vector. -/
theorem phase_linear_19_10 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 10 = (1 : ℤ) * n 4 + (-1 : ℤ) * n 22 + (5 : ℤ) * n 23 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_10]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 11; valid for every integer numerator vector. -/
theorem phase_linear_19_11 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 11 = (1 : ℤ) * n 5 + (1 : ℤ) * n 22 + (-1 : ℤ) * n 23 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_11]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 12; valid for every integer numerator vector. -/
theorem phase_linear_19_12 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 12 = (1 : ℤ) * n 0 + (-5 : ℤ) * n 1 + (10 : ℤ) * n 18 + (10 : ℤ) * n 19 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_12]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 13; valid for every integer numerator vector. -/
theorem phase_linear_19_13 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 13 = (-1 : ℤ) * n 0 + (1 : ℤ) * n 1 + (2 : ℤ) * n 18 + (10 : ℤ) * n 19 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_13]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 14; valid for every integer numerator vector. -/
theorem phase_linear_19_14 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 14 = (1 : ℤ) * n 2 + (-5 : ℤ) * n 3 + (10 : ℤ) * n 20 + (10 : ℤ) * n 21 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_14]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 15; valid for every integer numerator vector. -/
theorem phase_linear_19_15 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 15 = (-1 : ℤ) * n 2 + (1 : ℤ) * n 3 + (2 : ℤ) * n 20 + (10 : ℤ) * n 21 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_15]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 16; valid for every integer numerator vector. -/
theorem phase_linear_19_16 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 16 = (1 : ℤ) * n 4 + (-5 : ℤ) * n 5 + (10 : ℤ) * n 22 + (10 : ℤ) * n 23 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_16]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 17; valid for every integer numerator vector. -/
theorem phase_linear_19_17 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 17 = (-1 : ℤ) * n 4 + (1 : ℤ) * n 5 + (2 : ℤ) * n 22 + (10 : ℤ) * n 23 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_17]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 18; valid for every integer numerator vector. -/
theorem phase_linear_19_18 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 18 = (1 : ℤ) * n 6 + (-5 : ℤ) * n 7 + (1 : ℤ) * n 12 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_18]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 19; valid for every integer numerator vector. -/
theorem phase_linear_19_19 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 19 = (-1 : ℤ) * n 6 + (1 : ℤ) * n 7 + (1 : ℤ) * n 13 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_19]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 20; valid for every integer numerator vector. -/
theorem phase_linear_19_20 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 20 = (1 : ℤ) * n 8 + (-5 : ℤ) * n 9 + (1 : ℤ) * n 14 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_20]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 21; valid for every integer numerator vector. -/
theorem phase_linear_19_21 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 21 = (-1 : ℤ) * n 8 + (1 : ℤ) * n 9 + (1 : ℤ) * n 15 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_21]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 22; valid for every integer numerator vector. -/
theorem phase_linear_19_22 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 22 = (1 : ℤ) * n 10 + (-5 : ℤ) * n 11 + (1 : ℤ) * n 16 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_22]
  norm_num <;> ring

/-- Exact sparse phase 19, coordinate 23; valid for every integer numerator vector. -/
theorem phase_linear_19_23 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 19) 23 = (-1 : ℤ) * n 10 + (1 : ℤ) * n 11 + (1 : ℤ) * n 17 := by
  rw [phaseLinear_phase_literal_19, Scalar.mulNumerator, phaseLinear_terms_literal_23]
  norm_num <;> ring

end CGLMP5.SOSFinite
