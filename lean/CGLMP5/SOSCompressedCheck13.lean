import CGLMP5.SOSCompressedData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem source_phase_13_0 : ∀ k : Fin 24, canonicalCoefficient 13 0 k = core 26 k := by
  decide +kernel

theorem source_phase_13_1 : ∀ k : Fin 24, canonicalCoefficient 13 1 k = Scalar.mul (core 26) (phase 2) k := by
  decide +kernel

theorem source_phase_13_2 : ∀ k : Fin 24, canonicalCoefficient 13 2 k = core 27 k := by
  decide +kernel

theorem source_phase_13_3 : ∀ k : Fin 24, canonicalCoefficient 13 3 k = core 2 k := by
  decide +kernel

theorem source_phase_13_4 : ∀ k : Fin 24, canonicalCoefficient 13 4 k = Scalar.mul (core 2) (phase 1) k := by
  decide +kernel

theorem source_phase_13_5 : ∀ k : Fin 24, canonicalCoefficient 13 5 k = Scalar.mul (core 27) (phase 5) k := by
  decide +kernel

theorem source_phase_13_6 : ∀ k : Fin 24, canonicalCoefficient 13 6 k = Scalar.mul (core 26) (phase 9) k := by
  decide +kernel

theorem source_phase_13_7 : ∀ k : Fin 24, canonicalCoefficient 13 7 k = Scalar.mul (core 27) (phase 2) k := by
  decide +kernel

theorem source_phase_13_8 : ∀ k : Fin 24, canonicalCoefficient 13 8 k = Scalar.mul (core 2) (phase 11) k := by
  decide +kernel

theorem source_phase_13_9 : ∀ k : Fin 24, canonicalCoefficient 13 9 k = Scalar.mul (core 2) (phase 2) k := by
  decide +kernel

theorem source_phase_13_10 : ∀ k : Fin 24, canonicalCoefficient 13 10 k = Scalar.mul (core 27) (phase 11) k := by
  decide +kernel

theorem source_phase_13_11 : ∀ k : Fin 24, canonicalCoefficient 13 11 k = Scalar.mul (core 26) (phase 11) k := by
  decide +kernel

theorem gram_pair_126 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 2) k = gramPair 126 k := by
  decide +kernel

theorem gram_weight_126 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 13) (gramPair 126) k = gram 126 k := by
  decide +kernel

theorem gram_pair_127 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 26) k = gramPair 127 k := by
  decide +kernel

theorem gram_weight_127 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 13) (gramPair 127) k = gram 127 k := by
  decide +kernel

theorem gram_pair_128 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 27) k = gramPair 128 k := by
  decide +kernel

theorem gram_weight_128 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 13) (gramPair 128) k = gram 128 k := by
  decide +kernel

theorem gram_pair_129 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 26)) (core 2) k = gramPair 129 k := by
  decide +kernel

theorem gram_weight_129 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 13) (gramPair 129) k = gram 129 k := by
  decide +kernel

theorem gram_pair_130 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 26)) (core 26) k = gramPair 130 k := by
  decide +kernel

theorem gram_weight_130 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 13) (gramPair 130) k = gram 130 k := by
  decide +kernel

theorem gram_pair_131 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 26)) (core 27) k = gramPair 131 k := by
  decide +kernel

theorem gram_weight_131 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 13) (gramPair 131) k = gram 131 k := by
  decide +kernel

theorem gram_pair_132 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 27)) (core 2) k = gramPair 132 k := by
  decide +kernel

theorem gram_weight_132 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 13) (gramPair 132) k = gram 132 k := by
  decide +kernel

theorem gram_pair_133 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 27)) (core 26) k = gramPair 133 k := by
  decide +kernel

theorem gram_weight_133 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 13) (gramPair 133) k = gram 133 k := by
  decide +kernel

theorem gram_pair_134 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 27)) (core 27) k = gramPair 134 k := by
  decide +kernel

theorem gram_weight_134 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 13) (gramPair 134) k = gram 134 k := by
  decide +kernel


end CGLMP5.SOSFinite
