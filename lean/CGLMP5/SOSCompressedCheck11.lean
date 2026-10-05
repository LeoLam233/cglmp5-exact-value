import CGLMP5.SOSCompressedData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem source_phase_11_0 : ∀ k : Fin 24, canonicalCoefficient 11 0 k = core 2 k := by
  decide +kernel

theorem source_phase_11_1 : ∀ k : Fin 24, canonicalCoefficient 11 1 k = Scalar.mul (core 2) (phase 12) k := by
  decide +kernel

theorem source_phase_11_2 : ∀ k : Fin 24, canonicalCoefficient 11 2 k = Scalar.mul (core 2) (phase 12) k := by
  decide +kernel

theorem source_phase_11_3 : ∀ k : Fin 24, canonicalCoefficient 11 3 k = Scalar.mul (core 2) (phase 4) k := by
  decide +kernel

theorem gram_pair_109 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 2) k = gramPair 109 k := by
  decide +kernel

theorem gram_weight_109 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 11) (gramPair 109) k = gram 109 k := by
  decide +kernel


end CGLMP5.SOSFinite
