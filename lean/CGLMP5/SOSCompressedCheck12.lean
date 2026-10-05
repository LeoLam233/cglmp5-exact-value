import CGLMP5.SOSCompressedData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem source_phase_12_0 : ∀ k : Fin 24, canonicalCoefficient 12 0 k = core 23 k := by
  decide +kernel

theorem source_phase_12_1 : ∀ k : Fin 24, canonicalCoefficient 12 1 k = Scalar.mul (core 23) (phase 2) k := by
  decide +kernel

theorem source_phase_12_2 : ∀ k : Fin 24, canonicalCoefficient 12 2 k = core 24 k := by
  decide +kernel

theorem source_phase_12_3 : ∀ k : Fin 24, canonicalCoefficient 12 3 k = core 2 k := by
  decide +kernel

theorem source_phase_12_4 : ∀ k : Fin 24, canonicalCoefficient 12 4 k = core 25 k := by
  decide +kernel

theorem source_phase_12_5 : ∀ k : Fin 24, canonicalCoefficient 12 5 k = Scalar.mul (core 25) (phase 1) k := by
  decide +kernel

theorem source_phase_12_6 : ∀ k : Fin 24, canonicalCoefficient 12 6 k = Scalar.mul (core 2) (phase 3) k := by
  decide +kernel

theorem source_phase_12_7 : ∀ k : Fin 24, canonicalCoefficient 12 7 k = Scalar.mul (core 24) (phase 5) k := by
  decide +kernel

theorem source_phase_12_8 : ∀ k : Fin 24, canonicalCoefficient 12 8 k = Scalar.mul (core 23) (phase 9) k := by
  decide +kernel

theorem source_phase_12_9 : ∀ k : Fin 24, canonicalCoefficient 12 9 k = Scalar.mul (core 2) (phase 14) k := by
  decide +kernel

theorem source_phase_12_10 : ∀ k : Fin 24, canonicalCoefficient 12 10 k = Scalar.mul (core 24) (phase 2) k := by
  decide +kernel

theorem source_phase_12_11 : ∀ k : Fin 24, canonicalCoefficient 12 11 k = Scalar.mul (core 25) (phase 11) k := by
  decide +kernel

theorem source_phase_12_12 : ∀ k : Fin 24, canonicalCoefficient 12 12 k = Scalar.mul (core 25) (phase 2) k := by
  decide +kernel

theorem source_phase_12_13 : ∀ k : Fin 24, canonicalCoefficient 12 13 k = Scalar.mul (core 24) (phase 11) k := by
  decide +kernel

theorem source_phase_12_14 : ∀ k : Fin 24, canonicalCoefficient 12 14 k = Scalar.mul (core 2) (phase 5) k := by
  decide +kernel

theorem source_phase_12_15 : ∀ k : Fin 24, canonicalCoefficient 12 15 k = Scalar.mul (core 23) (phase 11) k := by
  decide +kernel

theorem gram_pair_110 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 2) k = gramPair 110 k := by
  decide +kernel

theorem gram_weight_110 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 110) k = gram 110 k := by
  decide +kernel

theorem gram_pair_111 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 23) k = gramPair 111 k := by
  decide +kernel

theorem gram_weight_111 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 111) k = gram 111 k := by
  decide +kernel

theorem gram_pair_112 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 24) k = gramPair 112 k := by
  decide +kernel

theorem gram_weight_112 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 112) k = gram 112 k := by
  decide +kernel

theorem gram_pair_113 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 25) k = gramPair 113 k := by
  decide +kernel

theorem gram_weight_113 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 113) k = gram 113 k := by
  decide +kernel

theorem gram_pair_114 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 23)) (core 2) k = gramPair 114 k := by
  decide +kernel

theorem gram_weight_114 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 114) k = gram 114 k := by
  decide +kernel

theorem gram_pair_115 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 23)) (core 23) k = gramPair 115 k := by
  decide +kernel

theorem gram_weight_115 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 115) k = gram 115 k := by
  decide +kernel

theorem gram_pair_116 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 23)) (core 24) k = gramPair 116 k := by
  decide +kernel

theorem gram_weight_116 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 116) k = gram 116 k := by
  decide +kernel

theorem gram_pair_117 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 23)) (core 25) k = gramPair 117 k := by
  decide +kernel

theorem gram_weight_117 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 117) k = gram 117 k := by
  decide +kernel

theorem gram_pair_118 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 24)) (core 2) k = gramPair 118 k := by
  decide +kernel

theorem gram_weight_118 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 118) k = gram 118 k := by
  decide +kernel

theorem gram_pair_119 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 24)) (core 23) k = gramPair 119 k := by
  decide +kernel

theorem gram_weight_119 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 119) k = gram 119 k := by
  decide +kernel

theorem gram_pair_120 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 24)) (core 24) k = gramPair 120 k := by
  decide +kernel

theorem gram_weight_120 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 120) k = gram 120 k := by
  decide +kernel

theorem gram_pair_121 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 24)) (core 25) k = gramPair 121 k := by
  decide +kernel

theorem gram_weight_121 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 121) k = gram 121 k := by
  decide +kernel

theorem gram_pair_122 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 25)) (core 2) k = gramPair 122 k := by
  decide +kernel

theorem gram_weight_122 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 122) k = gram 122 k := by
  decide +kernel

theorem gram_pair_123 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 25)) (core 23) k = gramPair 123 k := by
  decide +kernel

theorem gram_weight_123 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 123) k = gram 123 k := by
  decide +kernel

theorem gram_pair_124 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 25)) (core 24) k = gramPair 124 k := by
  decide +kernel

theorem gram_weight_124 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 124) k = gram 124 k := by
  decide +kernel

theorem gram_pair_125 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 25)) (core 25) k = gramPair 125 k := by
  decide +kernel

theorem gram_weight_125 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 12) (gramPair 125) k = gram 125 k := by
  decide +kernel


end CGLMP5.SOSFinite
