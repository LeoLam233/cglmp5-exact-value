import CGLMP5.SOSIntegerData
import CGLMP5.ScalarIntegerArithmetic

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def integerNumerator (w : Fin 273) (k : Fin 24) : ℤ :=
  ((fiber w).map fun f =>
    ((commonDenominator w / (gramDenominator f.1 * phaseDenominator f.2) : ℕ) : ℤ) *
      Scalar.mulNumerator (gramNumerator f.1) (phaseNumerator f.2) k).sum

/-- The exact coordinate proposition, kept named during finite-family assembly. -/
def integerCoordinateClaim (w : Fin 273) (k : Fin 24) : Prop :=
  integerNumerator w k * (targetDenominator w : Int) =
    targetNumerator w k * (commonDenominator w : Int)

/-- All24exact coordinates for one ordered normal word. -/
def integerResidualClaim (w : Fin 273) : Prop := ∀ k : Fin 24, integerCoordinateClaim w k

end CGLMP5.SOSFinite
