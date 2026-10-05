import CGLMP5.SOSCompressedData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem source_phase_9_0 : ∀ k : Fin 24, canonicalCoefficient 9 0 k = core 18 k := by
  decide +kernel

theorem source_phase_9_1 : ∀ k : Fin 24, canonicalCoefficient 9 1 k = Scalar.mul (core 18) (phase 4) k := by
  decide +kernel

theorem source_phase_9_2 : ∀ k : Fin 24, canonicalCoefficient 9 2 k = core 2 k := by
  decide +kernel

theorem source_phase_9_3 : ∀ k : Fin 24, canonicalCoefficient 9 3 k = core 19 k := by
  decide +kernel

theorem source_phase_9_4 : ∀ k : Fin 24, canonicalCoefficient 9 4 k = core 19 k := by
  decide +kernel

theorem source_phase_9_5 : ∀ k : Fin 24, canonicalCoefficient 9 5 k = Scalar.mul (core 2) (phase 4) k := by
  decide +kernel

theorem source_phase_9_6 : ∀ k : Fin 24, canonicalCoefficient 9 6 k = Scalar.mul (core 18) (phase 8) k := by
  decide +kernel

theorem source_phase_9_7 : ∀ k : Fin 24, canonicalCoefficient 9 7 k = core 20 k := by
  decide +kernel

theorem source_phase_9_8 : ∀ k : Fin 24, canonicalCoefficient 9 8 k = Scalar.mul (core 20) (phase 12) k := by
  decide +kernel

theorem source_phase_9_9 : ∀ k : Fin 24, canonicalCoefficient 9 9 k = Scalar.mul (core 19) (phase 12) k := by
  decide +kernel

theorem source_phase_9_10 : ∀ k : Fin 24, canonicalCoefficient 9 10 k = Scalar.mul (core 2) (phase 4) k := by
  decide +kernel

theorem source_phase_9_11 : ∀ k : Fin 24, canonicalCoefficient 9 11 k = Scalar.mul (core 2) (phase 12) k := by
  decide +kernel

theorem source_phase_9_12 : ∀ k : Fin 24, canonicalCoefficient 9 12 k = Scalar.mul (core 19) (phase 4) k := by
  decide +kernel

theorem source_phase_9_13 : ∀ k : Fin 24, canonicalCoefficient 9 13 k = Scalar.mul (core 18) (phase 12) k := by
  decide +kernel

theorem source_phase_9_14 : ∀ k : Fin 24, canonicalCoefficient 9 14 k = Scalar.mul (core 20) (phase 12) k := by
  decide +kernel

theorem source_phase_9_15 : ∀ k : Fin 24, canonicalCoefficient 9 15 k = Scalar.mul (core 20) (phase 4) k := by
  decide +kernel

theorem gram_pair_84 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 2) k = gramPair 84 k := by
  decide +kernel

theorem gram_weight_84 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 84) k = gram 84 k := by
  decide +kernel

theorem gram_pair_85 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 18) k = gramPair 85 k := by
  decide +kernel

theorem gram_weight_85 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 85) k = gram 85 k := by
  decide +kernel

theorem gram_pair_86 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 19) k = gramPair 86 k := by
  decide +kernel

theorem gram_weight_86 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 86) k = gram 86 k := by
  decide +kernel

theorem gram_pair_87 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 20) k = gramPair 87 k := by
  decide +kernel

theorem gram_weight_87 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 87) k = gram 87 k := by
  decide +kernel

theorem gram_pair_88 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 18)) (core 2) k = gramPair 88 k := by
  decide +kernel

theorem gram_weight_88 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 88) k = gram 88 k := by
  decide +kernel

theorem gram_pair_89 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 18)) (core 18) k = gramPair 89 k := by
  decide +kernel

theorem gram_weight_89 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 89) k = gram 89 k := by
  decide +kernel

theorem gram_pair_90 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 18)) (core 19) k = gramPair 90 k := by
  decide +kernel

theorem gram_weight_90 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 90) k = gram 90 k := by
  decide +kernel

theorem gram_pair_91 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 18)) (core 20) k = gramPair 91 k := by
  decide +kernel

theorem gram_weight_91 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 91) k = gram 91 k := by
  decide +kernel

theorem gram_pair_92 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 19)) (core 2) k = gramPair 92 k := by
  decide +kernel

theorem gram_weight_92 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 92) k = gram 92 k := by
  decide +kernel

theorem gram_pair_93 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 19)) (core 18) k = gramPair 93 k := by
  decide +kernel

theorem gram_weight_93 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 93) k = gram 93 k := by
  decide +kernel

theorem gram_pair_94 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 19)) (core 19) k = gramPair 94 k := by
  decide +kernel

theorem gram_weight_94 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 94) k = gram 94 k := by
  decide +kernel

theorem gram_pair_95 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 19)) (core 20) k = gramPair 95 k := by
  decide +kernel

theorem gram_weight_95 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 95) k = gram 95 k := by
  decide +kernel

theorem gram_pair_96 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 20)) (core 2) k = gramPair 96 k := by
  decide +kernel

theorem gram_weight_96 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 96) k = gram 96 k := by
  decide +kernel

theorem gram_pair_97 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 20)) (core 18) k = gramPair 97 k := by
  decide +kernel

theorem gram_weight_97 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 97) k = gram 97 k := by
  decide +kernel

theorem gram_pair_98 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 20)) (core 19) k = gramPair 98 k := by
  decide +kernel

theorem gram_weight_98 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 98) k = gram 98 k := by
  decide +kernel

theorem gram_pair_99 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 20)) (core 20) k = gramPair 99 k := by
  decide +kernel

theorem gram_weight_99 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 9) (gramPair 99) k = gram 99 k := by
  decide +kernel


end CGLMP5.SOSFinite
