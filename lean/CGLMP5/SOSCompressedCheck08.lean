import CGLMP5.SOSCompressedData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem source_phase_8_0 : ∀ k : Fin 24, canonicalCoefficient 8 0 k = core 17 k := by
  decide +kernel

theorem source_phase_8_1 : ∀ k : Fin 24, canonicalCoefficient 8 1 k = Scalar.mul (core 17) (phase 6) k := by
  decide +kernel

theorem source_phase_8_2 : ∀ k : Fin 24, canonicalCoefficient 8 2 k = Scalar.mul (core 17) (phase 7) k := by
  decide +kernel

theorem source_phase_8_3 : ∀ k : Fin 24, canonicalCoefficient 8 3 k = core 2 k := by
  decide +kernel

theorem source_phase_8_4 : ∀ k : Fin 24, canonicalCoefficient 8 4 k = Scalar.mul (core 2) (phase 9) k := by
  decide +kernel

theorem source_phase_8_5 : ∀ k : Fin 24, canonicalCoefficient 8 5 k = Scalar.mul (core 17) (phase 13) k := by
  decide +kernel

theorem source_phase_8_6 : ∀ k : Fin 24, canonicalCoefficient 8 6 k = Scalar.mul (core 2) (phase 2) k := by
  decide +kernel

theorem source_phase_8_7 : ∀ k : Fin 24, canonicalCoefficient 8 7 k = Scalar.mul (core 2) (phase 15) k := by
  decide +kernel

theorem gram_pair_80 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 2) k = gramPair 80 k := by
  decide +kernel

theorem gram_weight_80 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 8) (gramPair 80) k = gram 80 k := by
  decide +kernel

theorem gram_pair_81 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 17) k = gramPair 81 k := by
  decide +kernel

theorem gram_weight_81 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 8) (gramPair 81) k = gram 81 k := by
  decide +kernel

theorem gram_pair_82 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 17)) (core 2) k = gramPair 82 k := by
  decide +kernel

theorem gram_weight_82 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 8) (gramPair 82) k = gram 82 k := by
  decide +kernel

theorem gram_pair_83 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 17)) (core 17) k = gramPair 83 k := by
  decide +kernel

theorem gram_weight_83 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 8) (gramPair 83) k = gram 83 k := by
  decide +kernel


end CGLMP5.SOSFinite
