import CGLMP5.SOSCompressedData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem source_phase_6_0 : ∀ k : Fin 24, canonicalCoefficient 6 0 k = core 12 k := by
  decide +kernel

theorem source_phase_6_1 : ∀ k : Fin 24, canonicalCoefficient 6 1 k = Scalar.mul (core 12) (phase 6) k := by
  decide +kernel

theorem source_phase_6_2 : ∀ k : Fin 24, canonicalCoefficient 6 2 k = core 2 k := by
  decide +kernel

theorem source_phase_6_3 : ∀ k : Fin 24, canonicalCoefficient 6 3 k = Scalar.mul (core 2) (phase 3) k := by
  decide +kernel

theorem source_phase_6_4 : ∀ k : Fin 24, canonicalCoefficient 6 4 k = Scalar.mul (core 12) (phase 7) k := by
  decide +kernel

theorem source_phase_6_5 : ∀ k : Fin 24, canonicalCoefficient 6 5 k = core 13 k := by
  decide +kernel

theorem source_phase_6_6 : ∀ k : Fin 24, canonicalCoefficient 6 6 k = core 14 k := by
  decide +kernel

theorem source_phase_6_7 : ∀ k : Fin 24, canonicalCoefficient 6 7 k = Scalar.mul (core 14) (phase 9) k := by
  decide +kernel

theorem source_phase_6_8 : ∀ k : Fin 24, canonicalCoefficient 6 8 k = Scalar.mul (core 13) (phase 15) k := by
  decide +kernel

theorem source_phase_6_9 : ∀ k : Fin 24, canonicalCoefficient 6 9 k = Scalar.mul (core 2) (phase 13) k := by
  decide +kernel

theorem source_phase_6_10 : ∀ k : Fin 24, canonicalCoefficient 6 10 k = Scalar.mul (core 2) (phase 6) k := by
  decide +kernel

theorem source_phase_6_11 : ∀ k : Fin 24, canonicalCoefficient 6 11 k = Scalar.mul (core 12) (phase 13) k := by
  decide +kernel

theorem source_phase_6_12 : ∀ k : Fin 24, canonicalCoefficient 6 12 k = Scalar.mul (core 14) (phase 2) k := by
  decide +kernel

theorem source_phase_6_13 : ∀ k : Fin 24, canonicalCoefficient 6 13 k = Scalar.mul (core 13) (phase 6) k := by
  decide +kernel

theorem source_phase_6_14 : ∀ k : Fin 24, canonicalCoefficient 6 14 k = Scalar.mul (core 13) (phase 13) k := by
  decide +kernel

theorem source_phase_6_15 : ∀ k : Fin 24, canonicalCoefficient 6 15 k = Scalar.mul (core 14) (phase 15) k := by
  decide +kernel

theorem gram_pair_55 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 2) k = gramPair 55 k := by
  decide +kernel

theorem gram_weight_55 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 55) k = gram 55 k := by
  decide +kernel

theorem gram_pair_56 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 12) k = gramPair 56 k := by
  decide +kernel

theorem gram_weight_56 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 56) k = gram 56 k := by
  decide +kernel

theorem gram_pair_57 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 13) k = gramPair 57 k := by
  decide +kernel

theorem gram_weight_57 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 57) k = gram 57 k := by
  decide +kernel

theorem gram_pair_58 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 14) k = gramPair 58 k := by
  decide +kernel

theorem gram_weight_58 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 58) k = gram 58 k := by
  decide +kernel

theorem gram_pair_59 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 12)) (core 2) k = gramPair 59 k := by
  decide +kernel

theorem gram_weight_59 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 59) k = gram 59 k := by
  decide +kernel

theorem gram_pair_60 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 12)) (core 12) k = gramPair 60 k := by
  decide +kernel

theorem gram_weight_60 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 60) k = gram 60 k := by
  decide +kernel

theorem gram_pair_61 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 12)) (core 13) k = gramPair 61 k := by
  decide +kernel

theorem gram_weight_61 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 61) k = gram 61 k := by
  decide +kernel

theorem gram_pair_62 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 12)) (core 14) k = gramPair 62 k := by
  decide +kernel

theorem gram_weight_62 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 62) k = gram 62 k := by
  decide +kernel

theorem gram_pair_63 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 13)) (core 2) k = gramPair 63 k := by
  decide +kernel

theorem gram_weight_63 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 63) k = gram 63 k := by
  decide +kernel

theorem gram_pair_64 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 13)) (core 12) k = gramPair 64 k := by
  decide +kernel

theorem gram_weight_64 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 64) k = gram 64 k := by
  decide +kernel

theorem gram_pair_65 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 13)) (core 13) k = gramPair 65 k := by
  decide +kernel

theorem gram_weight_65 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 65) k = gram 65 k := by
  decide +kernel

theorem gram_pair_66 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 13)) (core 14) k = gramPair 66 k := by
  decide +kernel

theorem gram_weight_66 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 66) k = gram 66 k := by
  decide +kernel

theorem gram_pair_67 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 14)) (core 2) k = gramPair 67 k := by
  decide +kernel

theorem gram_weight_67 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 67) k = gram 67 k := by
  decide +kernel

theorem gram_pair_68 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 14)) (core 12) k = gramPair 68 k := by
  decide +kernel

theorem gram_weight_68 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 68) k = gram 68 k := by
  decide +kernel

theorem gram_pair_69 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 14)) (core 13) k = gramPair 69 k := by
  decide +kernel

theorem gram_weight_69 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 69) k = gram 69 k := by
  decide +kernel

theorem gram_pair_70 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 14)) (core 14) k = gramPair 70 k := by
  decide +kernel

theorem gram_weight_70 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 6) (gramPair 70) k = gram 70 k := by
  decide +kernel


end CGLMP5.SOSFinite
