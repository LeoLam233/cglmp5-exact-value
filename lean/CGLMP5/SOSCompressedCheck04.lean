import CGLMP5.SOSCompressedData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem source_phase_4_0 : ∀ k : Fin 24, canonicalCoefficient 4 0 k = core 2 k := by
  decide +kernel

theorem source_phase_4_1 : ∀ k : Fin 24, canonicalCoefficient 4 1 k = core 11 k := by
  decide +kernel

theorem source_phase_4_2 : ∀ k : Fin 24, canonicalCoefficient 4 2 k = Scalar.mul (core 11) (phase 14) k := by
  decide +kernel

theorem source_phase_4_3 : ∀ k : Fin 24, canonicalCoefficient 4 3 k = Scalar.mul (core 2) (phase 10) k := by
  decide +kernel

theorem source_phase_4_4 : ∀ k : Fin 24, canonicalCoefficient 4 4 k = Scalar.mul (core 2) (phase 4) k := by
  decide +kernel

theorem source_phase_4_5 : ∀ k : Fin 24, canonicalCoefficient 4 5 k = Scalar.mul (core 11) (phase 14) k := by
  decide +kernel

theorem source_phase_4_6 : ∀ k : Fin 24, canonicalCoefficient 4 6 k = Scalar.mul (core 11) (phase 8) k := by
  decide +kernel

theorem source_phase_4_7 : ∀ k : Fin 24, canonicalCoefficient 4 7 k = Scalar.mul (core 2) (phase 18) k := by
  decide +kernel

theorem gram_pair_50 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 2) k = gramPair 50 k := by
  decide +kernel

theorem gram_weight_50 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 4) (gramPair 50) k = gram 50 k := by
  decide +kernel

theorem gram_pair_51 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 11) k = gramPair 51 k := by
  decide +kernel

theorem gram_weight_51 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 4) (gramPair 51) k = gram 51 k := by
  decide +kernel

theorem gram_pair_52 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 11)) (core 2) k = gramPair 52 k := by
  decide +kernel

theorem gram_weight_52 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 4) (gramPair 52) k = gram 52 k := by
  decide +kernel

theorem gram_pair_53 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 11)) (core 11) k = gramPair 53 k := by
  decide +kernel

theorem gram_weight_53 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 4) (gramPair 53) k = gram 53 k := by
  decide +kernel


end CGLMP5.SOSFinite
