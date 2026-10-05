import CGLMP5.SOSPhaseLinearData
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Exact sparse phase 12, coordinate 0; valid for every integer numerator vector. -/
theorem phase_linear_12_0 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 0 = (-2 : ℤ) * n 0 + (-10 : ℤ) * n 1 + (40 : ℤ) * n 19 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_0]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 1; valid for every integer numerator vector. -/
theorem phase_linear_12_1 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 1 = (-2 : ℤ) * n 0 + (-2 : ℤ) * n 1 + (8 : ℤ) * n 18 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_1]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 2; valid for every integer numerator vector. -/
theorem phase_linear_12_2 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 2 = (-2 : ℤ) * n 2 + (-10 : ℤ) * n 3 + (40 : ℤ) * n 21 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_2]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 3; valid for every integer numerator vector. -/
theorem phase_linear_12_3 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 3 = (-2 : ℤ) * n 2 + (-2 : ℤ) * n 3 + (8 : ℤ) * n 20 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_3]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 4; valid for every integer numerator vector. -/
theorem phase_linear_12_4 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 4 = (-2 : ℤ) * n 4 + (-10 : ℤ) * n 5 + (40 : ℤ) * n 23 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_4]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 5; valid for every integer numerator vector. -/
theorem phase_linear_12_5 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 5 = (-2 : ℤ) * n 4 + (-2 : ℤ) * n 5 + (8 : ℤ) * n 22 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_5]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 6; valid for every integer numerator vector. -/
theorem phase_linear_12_6 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 6 = (-2 : ℤ) * n 6 + (-10 : ℤ) * n 7 + (-1 : ℤ) * n 12 + (5 : ℤ) * n 13 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_6]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 7; valid for every integer numerator vector. -/
theorem phase_linear_12_7 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 7 = (-2 : ℤ) * n 6 + (-2 : ℤ) * n 7 + (1 : ℤ) * n 12 + (-1 : ℤ) * n 13 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_7]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 8; valid for every integer numerator vector. -/
theorem phase_linear_12_8 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 8 = (-2 : ℤ) * n 8 + (-10 : ℤ) * n 9 + (-1 : ℤ) * n 14 + (5 : ℤ) * n 15 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_8]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 9; valid for every integer numerator vector. -/
theorem phase_linear_12_9 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 9 = (-2 : ℤ) * n 8 + (-2 : ℤ) * n 9 + (1 : ℤ) * n 14 + (-1 : ℤ) * n 15 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_9]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 10; valid for every integer numerator vector. -/
theorem phase_linear_12_10 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 10 = (-2 : ℤ) * n 10 + (-10 : ℤ) * n 11 + (-1 : ℤ) * n 16 + (5 : ℤ) * n 17 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_10]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 11; valid for every integer numerator vector. -/
theorem phase_linear_12_11 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 11 = (-2 : ℤ) * n 10 + (-2 : ℤ) * n 11 + (1 : ℤ) * n 16 + (-1 : ℤ) * n 17 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_11]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 12; valid for every integer numerator vector. -/
theorem phase_linear_12_12 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 12 = (-40 : ℤ) * n 7 + (-2 : ℤ) * n 12 + (-10 : ℤ) * n 13 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_12]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 13; valid for every integer numerator vector. -/
theorem phase_linear_12_13 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 13 = (-8 : ℤ) * n 6 + (-2 : ℤ) * n 12 + (-2 : ℤ) * n 13 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_13]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 14; valid for every integer numerator vector. -/
theorem phase_linear_12_14 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 14 = (-40 : ℤ) * n 9 + (-2 : ℤ) * n 14 + (-10 : ℤ) * n 15 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_14]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 15; valid for every integer numerator vector. -/
theorem phase_linear_12_15 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 15 = (-8 : ℤ) * n 8 + (-2 : ℤ) * n 14 + (-2 : ℤ) * n 15 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_15]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 16; valid for every integer numerator vector. -/
theorem phase_linear_12_16 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 16 = (-40 : ℤ) * n 11 + (-2 : ℤ) * n 16 + (-10 : ℤ) * n 17 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_16]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 17; valid for every integer numerator vector. -/
theorem phase_linear_12_17 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 17 = (-8 : ℤ) * n 10 + (-2 : ℤ) * n 16 + (-2 : ℤ) * n 17 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_17]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 18; valid for every integer numerator vector. -/
theorem phase_linear_12_18 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 18 = (1 : ℤ) * n 0 + (-5 : ℤ) * n 1 + (-2 : ℤ) * n 18 + (-10 : ℤ) * n 19 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_18]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 19; valid for every integer numerator vector. -/
theorem phase_linear_12_19 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 19 = (-1 : ℤ) * n 0 + (1 : ℤ) * n 1 + (-2 : ℤ) * n 18 + (-2 : ℤ) * n 19 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_19]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 20; valid for every integer numerator vector. -/
theorem phase_linear_12_20 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 20 = (1 : ℤ) * n 2 + (-5 : ℤ) * n 3 + (-2 : ℤ) * n 20 + (-10 : ℤ) * n 21 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_20]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 21; valid for every integer numerator vector. -/
theorem phase_linear_12_21 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 21 = (-1 : ℤ) * n 2 + (1 : ℤ) * n 3 + (-2 : ℤ) * n 20 + (-2 : ℤ) * n 21 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_21]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 22; valid for every integer numerator vector. -/
theorem phase_linear_12_22 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 22 = (1 : ℤ) * n 4 + (-5 : ℤ) * n 5 + (-2 : ℤ) * n 22 + (-10 : ℤ) * n 23 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_22]
  norm_num <;> ring

/-- Exact sparse phase 12, coordinate 23; valid for every integer numerator vector. -/
theorem phase_linear_12_23 (n : Fin 24 → ℤ) :
    Scalar.mulNumerator n (phaseNumerator 12) 23 = (-1 : ℤ) * n 4 + (1 : ℤ) * n 5 + (-2 : ℤ) * n 22 + (-2 : ℤ) * n 23 := by
  rw [phaseLinear_phase_literal_12, Scalar.mulNumerator, phaseLinear_terms_literal_23]
  norm_num <;> ring

end CGLMP5.SOSFinite
