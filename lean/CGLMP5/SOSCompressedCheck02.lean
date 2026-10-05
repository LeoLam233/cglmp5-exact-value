import CGLMP5.SOSCompressedData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem source_phase_2_0 : ∀ k : Fin 24, canonicalCoefficient 2 0 k = core 2 k := by
  decide +kernel

theorem source_phase_2_1 : ∀ k : Fin 24, canonicalCoefficient 2 1 k = Scalar.mul (core 2) (phase 8) k := by
  decide +kernel

theorem source_phase_2_2 : ∀ k : Fin 24, canonicalCoefficient 2 2 k = Scalar.mul (core 2) (phase 6) k := by
  decide +kernel

theorem source_phase_2_3 : ∀ k : Fin 24, canonicalCoefficient 2 3 k = core 6 k := by
  decide +kernel

theorem source_phase_2_4 : ∀ k : Fin 24, canonicalCoefficient 2 4 k = core 7 k := by
  decide +kernel

theorem source_phase_2_5 : ∀ k : Fin 24, canonicalCoefficient 2 5 k = core 8 k := by
  decide +kernel

theorem source_phase_2_6 : ∀ k : Fin 24, canonicalCoefficient 2 6 k = Scalar.mul (core 8) (phase 14) k := by
  decide +kernel

theorem source_phase_2_7 : ∀ k : Fin 24, canonicalCoefficient 2 7 k = Scalar.mul (core 7) (phase 10) k := by
  decide +kernel

theorem source_phase_2_8 : ∀ k : Fin 24, canonicalCoefficient 2 8 k = Scalar.mul (core 6) (phase 18) k := by
  decide +kernel

theorem source_phase_2_9 : ∀ k : Fin 24, canonicalCoefficient 2 9 k = Scalar.mul (core 2) (phase 14) k := by
  decide +kernel

theorem source_phase_2_10 : ∀ k : Fin 24, canonicalCoefficient 2 10 k = Scalar.mul (core 7) (phase 4) k := by
  decide +kernel

theorem source_phase_2_11 : ∀ k : Fin 24, canonicalCoefficient 2 11 k = Scalar.mul (core 6) (phase 8) k := by
  decide +kernel

theorem source_phase_2_12 : ∀ k : Fin 24, canonicalCoefficient 2 12 k = Scalar.mul (core 8) (phase 14) k := by
  decide +kernel

theorem source_phase_2_13 : ∀ k : Fin 24, canonicalCoefficient 2 13 k = Scalar.mul (core 8) (phase 8) k := by
  decide +kernel

theorem source_phase_2_14 : ∀ k : Fin 24, canonicalCoefficient 2 14 k = Scalar.mul (core 6) (phase 14) k := by
  decide +kernel

theorem source_phase_2_15 : ∀ k : Fin 24, canonicalCoefficient 2 15 k = Scalar.mul (core 7) (phase 18) k := by
  decide +kernel

theorem gram_pair_25 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 2) k = gramPair 25 k := by
  decide +kernel

theorem gram_weight_25 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 25) k = gram 25 k := by
  decide +kernel

theorem gram_pair_26 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 6) k = gramPair 26 k := by
  decide +kernel

theorem gram_weight_26 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 26) k = gram 26 k := by
  decide +kernel

theorem gram_pair_27 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 7) k = gramPair 27 k := by
  decide +kernel

theorem gram_weight_27 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 27) k = gram 27 k := by
  decide +kernel

theorem gram_pair_28 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 8) k = gramPair 28 k := by
  decide +kernel

theorem gram_weight_28 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 28) k = gram 28 k := by
  decide +kernel

theorem gram_pair_29 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 6)) (core 2) k = gramPair 29 k := by
  decide +kernel

theorem gram_weight_29 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 29) k = gram 29 k := by
  decide +kernel

theorem gram_pair_30 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 6)) (core 6) k = gramPair 30 k := by
  decide +kernel

theorem gram_weight_30 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 30) k = gram 30 k := by
  decide +kernel

theorem gram_pair_31 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 6)) (core 7) k = gramPair 31 k := by
  decide +kernel

theorem gram_weight_31 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 31) k = gram 31 k := by
  decide +kernel

theorem gram_pair_32 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 6)) (core 8) k = gramPair 32 k := by
  decide +kernel

theorem gram_weight_32 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 32) k = gram 32 k := by
  decide +kernel

theorem gram_pair_33 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 7)) (core 2) k = gramPair 33 k := by
  decide +kernel

theorem gram_weight_33 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 33) k = gram 33 k := by
  decide +kernel

theorem gram_pair_34 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 7)) (core 6) k = gramPair 34 k := by
  decide +kernel

theorem gram_weight_34 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 34) k = gram 34 k := by
  decide +kernel

theorem gram_pair_35 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 7)) (core 7) k = gramPair 35 k := by
  decide +kernel

theorem gram_weight_35 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 35) k = gram 35 k := by
  decide +kernel

theorem gram_pair_36 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 7)) (core 8) k = gramPair 36 k := by
  decide +kernel

theorem gram_weight_36 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 36) k = gram 36 k := by
  decide +kernel

theorem gram_pair_37 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 8)) (core 2) k = gramPair 37 k := by
  decide +kernel

theorem gram_weight_37 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 37) k = gram 37 k := by
  decide +kernel

theorem gram_pair_38 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 8)) (core 6) k = gramPair 38 k := by
  decide +kernel

theorem gram_weight_38 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 38) k = gram 38 k := by
  decide +kernel

theorem gram_pair_39 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 8)) (core 7) k = gramPair 39 k := by
  decide +kernel

theorem gram_weight_39 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 39) k = gram 39 k := by
  decide +kernel

theorem gram_pair_40 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 8)) (core 8) k = gramPair 40 k := by
  decide +kernel

theorem gram_weight_40 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 2) (gramPair 40) k = gram 40 k := by
  decide +kernel


end CGLMP5.SOSFinite
