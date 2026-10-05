import CGLMP5.SOSCompressedData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem source_phase_5_0 : ∀ k : Fin 24, canonicalCoefficient 5 0 k = core 2 k := by
  decide +kernel

theorem source_phase_5_1 : ∀ k : Fin 24, canonicalCoefficient 5 1 k = Scalar.mul (core 2) (phase 14) k := by
  decide +kernel

theorem source_phase_5_2 : ∀ k : Fin 24, canonicalCoefficient 5 2 k = Scalar.mul (core 2) (phase 14) k := by
  decide +kernel

theorem source_phase_5_3 : ∀ k : Fin 24, canonicalCoefficient 5 3 k = Scalar.mul (core 2) (phase 8) k := by
  decide +kernel

theorem gram_pair_54 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 2) k = gramPair 54 k := by
  decide +kernel

theorem gram_weight_54 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 5) (gramPair 54) k = gram 54 k := by
  decide +kernel


end CGLMP5.SOSFinite
