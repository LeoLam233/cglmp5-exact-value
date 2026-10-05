import CGLMP5.SOSCompressedData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem source_phase_1_0 : ∀ k : Fin 24, canonicalCoefficient 1 0 k = core 4 k := by
  decide +kernel

theorem source_phase_1_1 : ∀ k : Fin 24, canonicalCoefficient 1 1 k = Scalar.mul (core 4) (phase 18) k := by
  decide +kernel

theorem source_phase_1_2 : ∀ k : Fin 24, canonicalCoefficient 1 2 k = Scalar.mul (core 4) (phase 1) k := by
  decide +kernel

theorem source_phase_1_3 : ∀ k : Fin 24, canonicalCoefficient 1 3 k = core 5 k := by
  decide +kernel

theorem source_phase_1_4 : ∀ k : Fin 24, canonicalCoefficient 1 4 k = core 2 k := by
  decide +kernel

theorem source_phase_1_5 : ∀ k : Fin 24, canonicalCoefficient 1 5 k = Scalar.mul (core 2) (phase 9) k := by
  decide +kernel

theorem source_phase_1_6 : ∀ k : Fin 24, canonicalCoefficient 1 6 k = Scalar.mul (core 5) (phase 13) k := by
  decide +kernel

theorem source_phase_1_7 : ∀ k : Fin 24, canonicalCoefficient 1 7 k = Scalar.mul (core 4) (phase 19) k := by
  decide +kernel

theorem source_phase_1_8 : ∀ k : Fin 24, canonicalCoefficient 1 8 k = Scalar.mul (core 5) (phase 18) k := by
  decide +kernel

theorem source_phase_1_9 : ∀ k : Fin 24, canonicalCoefficient 1 9 k = Scalar.mul (core 2) (phase 19) k := by
  decide +kernel

theorem source_phase_1_10 : ∀ k : Fin 24, canonicalCoefficient 1 10 k = Scalar.mul (core 2) (phase 18) k := by
  decide +kernel

theorem source_phase_1_11 : ∀ k : Fin 24, canonicalCoefficient 1 11 k = Scalar.mul (core 5) (phase 19) k := by
  decide +kernel

theorem gram_pair_16 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 2) k = gramPair 16 k := by
  decide +kernel

theorem gram_weight_16 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 1) (gramPair 16) k = gram 16 k := by
  decide +kernel

theorem gram_pair_17 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 4) k = gramPair 17 k := by
  decide +kernel

theorem gram_weight_17 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 1) (gramPair 17) k = gram 17 k := by
  decide +kernel

theorem gram_pair_18 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 5) k = gramPair 18 k := by
  decide +kernel

theorem gram_weight_18 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 1) (gramPair 18) k = gram 18 k := by
  decide +kernel

theorem gram_pair_19 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 4)) (core 2) k = gramPair 19 k := by
  decide +kernel

theorem gram_weight_19 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 1) (gramPair 19) k = gram 19 k := by
  decide +kernel

theorem gram_pair_20 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 4)) (core 4) k = gramPair 20 k := by
  decide +kernel

theorem gram_weight_20 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 1) (gramPair 20) k = gram 20 k := by
  decide +kernel

theorem gram_pair_21 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 4)) (core 5) k = gramPair 21 k := by
  decide +kernel

theorem gram_weight_21 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 1) (gramPair 21) k = gram 21 k := by
  decide +kernel

theorem gram_pair_22 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 5)) (core 2) k = gramPair 22 k := by
  decide +kernel

theorem gram_weight_22 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 1) (gramPair 22) k = gram 22 k := by
  decide +kernel

theorem gram_pair_23 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 5)) (core 4) k = gramPair 23 k := by
  decide +kernel

theorem gram_weight_23 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 1) (gramPair 23) k = gram 23 k := by
  decide +kernel

theorem gram_pair_24 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 5)) (core 5) k = gramPair 24 k := by
  decide +kernel

theorem gram_weight_24 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 1) (gramPair 24) k = gram 24 k := by
  decide +kernel


end CGLMP5.SOSFinite
