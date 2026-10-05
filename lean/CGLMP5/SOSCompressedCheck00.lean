import CGLMP5.SOSCompressedData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem source_phase_0_0 : ∀ k : Fin 24, canonicalCoefficient 0 0 k = core 0 k := by
  decide +kernel

theorem source_phase_0_1 : ∀ k : Fin 24, canonicalCoefficient 0 1 k = Scalar.mul (core 0) (phase 18) k := by
  decide +kernel

theorem source_phase_0_2 : ∀ k : Fin 24, canonicalCoefficient 0 2 k = Scalar.mul (core 0) (phase 1) k := by
  decide +kernel

theorem source_phase_0_3 : ∀ k : Fin 24, canonicalCoefficient 0 3 k = core 1 k := by
  decide +kernel

theorem source_phase_0_4 : ∀ k : Fin 24, canonicalCoefficient 0 4 k = core 2 k := by
  decide +kernel

theorem source_phase_0_5 : ∀ k : Fin 24, canonicalCoefficient 0 5 k = core 3 k := by
  decide +kernel

theorem source_phase_0_6 : ∀ k : Fin 24, canonicalCoefficient 0 6 k = Scalar.mul (core 3) (phase 9) k := by
  decide +kernel

theorem source_phase_0_7 : ∀ k : Fin 24, canonicalCoefficient 0 7 k = Scalar.mul (core 2) (phase 15) k := by
  decide +kernel

theorem source_phase_0_8 : ∀ k : Fin 24, canonicalCoefficient 0 8 k = Scalar.mul (core 1) (phase 13) k := by
  decide +kernel

theorem source_phase_0_9 : ∀ k : Fin 24, canonicalCoefficient 0 9 k = Scalar.mul (core 0) (phase 19) k := by
  decide +kernel

theorem source_phase_0_10 : ∀ k : Fin 24, canonicalCoefficient 0 10 k = Scalar.mul (core 2) (phase 14) k := by
  decide +kernel

theorem source_phase_0_11 : ∀ k : Fin 24, canonicalCoefficient 0 11 k = Scalar.mul (core 1) (phase 18) k := by
  decide +kernel

theorem source_phase_0_12 : ∀ k : Fin 24, canonicalCoefficient 0 12 k = Scalar.mul (core 3) (phase 19) k := by
  decide +kernel

theorem source_phase_0_13 : ∀ k : Fin 24, canonicalCoefficient 0 13 k = Scalar.mul (core 3) (phase 18) k := by
  decide +kernel

theorem source_phase_0_14 : ∀ k : Fin 24, canonicalCoefficient 0 14 k = Scalar.mul (core 1) (phase 19) k := by
  decide +kernel

theorem source_phase_0_15 : ∀ k : Fin 24, canonicalCoefficient 0 15 k = Scalar.mul (core 2) (phase 13) k := by
  decide +kernel

theorem gram_pair_0 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 0)) (core 0) k = gramPair 0 k := by
  decide +kernel

theorem gram_weight_0 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 0) k = gram 0 k := by
  decide +kernel

theorem gram_pair_1 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 0)) (core 1) k = gramPair 1 k := by
  decide +kernel

theorem gram_weight_1 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 1) k = gram 1 k := by
  decide +kernel

theorem gram_pair_2 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 0)) (core 2) k = gramPair 2 k := by
  decide +kernel

theorem gram_weight_2 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 2) k = gram 2 k := by
  decide +kernel

theorem gram_pair_3 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 0)) (core 3) k = gramPair 3 k := by
  decide +kernel

theorem gram_weight_3 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 3) k = gram 3 k := by
  decide +kernel

theorem gram_pair_4 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 1)) (core 0) k = gramPair 4 k := by
  decide +kernel

theorem gram_weight_4 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 4) k = gram 4 k := by
  decide +kernel

theorem gram_pair_5 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 1)) (core 1) k = gramPair 5 k := by
  decide +kernel

theorem gram_weight_5 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 5) k = gram 5 k := by
  decide +kernel

theorem gram_pair_6 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 1)) (core 2) k = gramPair 6 k := by
  decide +kernel

theorem gram_weight_6 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 6) k = gram 6 k := by
  decide +kernel

theorem gram_pair_7 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 1)) (core 3) k = gramPair 7 k := by
  decide +kernel

theorem gram_weight_7 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 7) k = gram 7 k := by
  decide +kernel

theorem gram_pair_8 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 0) k = gramPair 8 k := by
  decide +kernel

theorem gram_weight_8 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 8) k = gram 8 k := by
  decide +kernel

theorem gram_pair_9 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 1) k = gramPair 9 k := by
  decide +kernel

theorem gram_weight_9 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 9) k = gram 9 k := by
  decide +kernel

theorem gram_pair_10 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 2) k = gramPair 10 k := by
  decide +kernel

theorem gram_weight_10 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 10) k = gram 10 k := by
  decide +kernel

theorem gram_pair_11 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 3) k = gramPair 11 k := by
  decide +kernel

theorem gram_weight_11 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 11) k = gram 11 k := by
  decide +kernel

theorem gram_pair_12 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 3)) (core 0) k = gramPair 12 k := by
  decide +kernel

theorem gram_weight_12 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 12) k = gram 12 k := by
  decide +kernel

theorem gram_pair_13 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 3)) (core 1) k = gramPair 13 k := by
  decide +kernel

theorem gram_weight_13 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 13) k = gram 13 k := by
  decide +kernel

theorem gram_pair_14 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 3)) (core 2) k = gramPair 14 k := by
  decide +kernel

theorem gram_weight_14 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 14) k = gram 14 k := by
  decide +kernel

theorem gram_pair_15 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 3)) (core 3) k = gramPair 15 k := by
  decide +kernel

theorem gram_weight_15 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 0) (gramPair 15) k = gram 15 k := by
  decide +kernel


end CGLMP5.SOSFinite
