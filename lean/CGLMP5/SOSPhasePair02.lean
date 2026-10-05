import CGLMP5.SOSCompressedData
namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Exact phase-pair identities for fixed first phase 2, with all second phases and coordinates. -/
theorem phase_pair_row_2 : ∀ (q : Fin 20) (k : Fin 24),
    Scalar.mul (Scalar.conj (phase 2)) (phase q) k = phase (phaseDifference 2 q) k := by
  decide +kernel

end CGLMP5.SOSFinite
