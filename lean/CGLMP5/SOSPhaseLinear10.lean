import CGLMP5.SOSPhaseLinearData
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Exact sparse phase 10, coordinate 0; valid for every integer numerator vector. -/
theorem phase_linear_10_0 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 0 = (-1 : ℤ) * n 0 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_0]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 1; valid for every integer numerator vector. -/
theorem phase_linear_10_1 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 1 = (-1 : ℤ) * n 1 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_1]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 2; valid for every integer numerator vector. -/
theorem phase_linear_10_2 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 2 = (-1 : ℤ) * n 2 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_2]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 3; valid for every integer numerator vector. -/
theorem phase_linear_10_3 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 3 = (-1 : ℤ) * n 3 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_3]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 4; valid for every integer numerator vector. -/
theorem phase_linear_10_4 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 4 = (-1 : ℤ) * n 4 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_4]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 5; valid for every integer numerator vector. -/
theorem phase_linear_10_5 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 5 = (-1 : ℤ) * n 5 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_5]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 6; valid for every integer numerator vector. -/
theorem phase_linear_10_6 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 6 = (-1 : ℤ) * n 6 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_6]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 7; valid for every integer numerator vector. -/
theorem phase_linear_10_7 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 7 = (-1 : ℤ) * n 7 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_7]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 8; valid for every integer numerator vector. -/
theorem phase_linear_10_8 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 8 = (-1 : ℤ) * n 8 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_8]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 9; valid for every integer numerator vector. -/
theorem phase_linear_10_9 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 9 = (-1 : ℤ) * n 9 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_9]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 10; valid for every integer numerator vector. -/
theorem phase_linear_10_10 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 10 = (-1 : ℤ) * n 10 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_10]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 11; valid for every integer numerator vector. -/
theorem phase_linear_10_11 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 11 = (-1 : ℤ) * n 11 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_11]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 12; valid for every integer numerator vector. -/
theorem phase_linear_10_12 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 12 = (-1 : ℤ) * n 12 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_12]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 13; valid for every integer numerator vector. -/
theorem phase_linear_10_13 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 13 = (-1 : ℤ) * n 13 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_13]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 14; valid for every integer numerator vector. -/
theorem phase_linear_10_14 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 14 = (-1 : ℤ) * n 14 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_14]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 15; valid for every integer numerator vector. -/
theorem phase_linear_10_15 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 15 = (-1 : ℤ) * n 15 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_15]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 16; valid for every integer numerator vector. -/
theorem phase_linear_10_16 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 16 = (-1 : ℤ) * n 16 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_16]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 17; valid for every integer numerator vector. -/
theorem phase_linear_10_17 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 17 = (-1 : ℤ) * n 17 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_17]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 18; valid for every integer numerator vector. -/
theorem phase_linear_10_18 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 18 = (-1 : ℤ) * n 18 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_18]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 19; valid for every integer numerator vector. -/
theorem phase_linear_10_19 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 19 = (-1 : ℤ) * n 19 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_19]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 20; valid for every integer numerator vector. -/
theorem phase_linear_10_20 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 20 = (-1 : ℤ) * n 20 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_20]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 21; valid for every integer numerator vector. -/
theorem phase_linear_10_21 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 21 = (-1 : ℤ) * n 21 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_21]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 22; valid for every integer numerator vector. -/
theorem phase_linear_10_22 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 22 = (-1 : ℤ) * n 22 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_22]
  norm_num <;> ring

/-- Exact sparse phase 10, coordinate 23; valid for every integer numerator vector. -/
theorem phase_linear_10_23 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 10) 23 = (-1 : ℤ) * n 23 := by
  rw [phaseLinear_phase_literal_10, Scalar.mulNumerator, phaseLinear_terms_literal_23]
  norm_num <;> ring

end CGLMP5.SOSFinite
