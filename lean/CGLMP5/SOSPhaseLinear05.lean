import CGLMP5.SOSPhaseLinearData
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Exact sparse phase 5, coordinate 0; valid for every integer numerator vector. -/
theorem phase_linear_5_0 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 0 = (-1 : ℤ) * n 12 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_0]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 1; valid for every integer numerator vector. -/
theorem phase_linear_5_1 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 1 = (-1 : ℤ) * n 13 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_1]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 2; valid for every integer numerator vector. -/
theorem phase_linear_5_2 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 2 = (-1 : ℤ) * n 14 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_2]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 3; valid for every integer numerator vector. -/
theorem phase_linear_5_3 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 3 = (-1 : ℤ) * n 15 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_3]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 4; valid for every integer numerator vector. -/
theorem phase_linear_5_4 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 4 = (-1 : ℤ) * n 16 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_4]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 5; valid for every integer numerator vector. -/
theorem phase_linear_5_5 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 5 = (-1 : ℤ) * n 17 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_5]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 6; valid for every integer numerator vector. -/
theorem phase_linear_5_6 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 6 = (-1 : ℤ) * n 18 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_6]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 7; valid for every integer numerator vector. -/
theorem phase_linear_5_7 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 7 = (-1 : ℤ) * n 19 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_7]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 8; valid for every integer numerator vector. -/
theorem phase_linear_5_8 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 8 = (-1 : ℤ) * n 20 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_8]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 9; valid for every integer numerator vector. -/
theorem phase_linear_5_9 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 9 = (-1 : ℤ) * n 21 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_9]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 10; valid for every integer numerator vector. -/
theorem phase_linear_5_10 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 10 = (-1 : ℤ) * n 22 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_10]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 11; valid for every integer numerator vector. -/
theorem phase_linear_5_11 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 11 = (-1 : ℤ) * n 23 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_11]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 12; valid for every integer numerator vector. -/
theorem phase_linear_5_12 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 12 = (1 : ℤ) * n 0 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_12]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 13; valid for every integer numerator vector. -/
theorem phase_linear_5_13 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 13 = (1 : ℤ) * n 1 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_13]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 14; valid for every integer numerator vector. -/
theorem phase_linear_5_14 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 14 = (1 : ℤ) * n 2 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_14]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 15; valid for every integer numerator vector. -/
theorem phase_linear_5_15 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 15 = (1 : ℤ) * n 3 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_15]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 16; valid for every integer numerator vector. -/
theorem phase_linear_5_16 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 16 = (1 : ℤ) * n 4 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_16]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 17; valid for every integer numerator vector. -/
theorem phase_linear_5_17 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 17 = (1 : ℤ) * n 5 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_17]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 18; valid for every integer numerator vector. -/
theorem phase_linear_5_18 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 18 = (1 : ℤ) * n 6 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_18]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 19; valid for every integer numerator vector. -/
theorem phase_linear_5_19 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 19 = (1 : ℤ) * n 7 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_19]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 20; valid for every integer numerator vector. -/
theorem phase_linear_5_20 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 20 = (1 : ℤ) * n 8 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_20]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 21; valid for every integer numerator vector. -/
theorem phase_linear_5_21 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 21 = (1 : ℤ) * n 9 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_21]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 22; valid for every integer numerator vector. -/
theorem phase_linear_5_22 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 22 = (1 : ℤ) * n 10 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_22]
  norm_num <;> ring

/-- Exact sparse phase 5, coordinate 23; valid for every integer numerator vector. -/
theorem phase_linear_5_23 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 5) 23 = (1 : ℤ) * n 11 := by
  rw [phaseLinear_phase_literal_5, Scalar.mulNumerator, phaseLinear_terms_literal_23]
  norm_num <;> ring

end CGLMP5.SOSFinite
