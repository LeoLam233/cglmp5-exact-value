import Mathlib.Data.Fintype.Fin
import CGLMP5.SOSIntegerData
import Mathlib.Tactic.FinCases

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem gram_as_canonical (i : Fin 135) : gram i = Scalar.ofCanonical (gramNumerator i) (gramDenominator i) := by
  funext k
  fin_cases i <;> first | rfl | (fin_cases k <;> simp [targetAt, targetNumerator, targetDenominator, Scalar.zero, Scalar.ofCanonical])

theorem phase_as_canonical (i : Fin 20) : phase i = Scalar.ofCanonical (phaseNumerator i) (phaseDenominator i) := by
  funext k
  fin_cases i <;> first | rfl | (fin_cases k <;> simp [targetAt, targetNumerator, targetDenominator, Scalar.zero, Scalar.ofCanonical])

theorem target_as_canonical (i : Fin 273) : targetAt i = Scalar.ofCanonical (targetNumerator i) (targetDenominator i) := by
  funext k
  revert i k
  decide +kernel



end CGLMP5.SOSFinite
