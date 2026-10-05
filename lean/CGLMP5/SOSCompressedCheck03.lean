import CGLMP5.SOSCompressedData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem source_phase_3_0 : ∀ k : Fin 24, canonicalCoefficient 3 0 k = core 2 k := by
  decide +kernel

theorem source_phase_3_1 : ∀ k : Fin 24, canonicalCoefficient 3 1 k = core 9 k := by
  decide +kernel

theorem source_phase_3_2 : ∀ k : Fin 24, canonicalCoefficient 3 2 k = core 10 k := by
  decide +kernel

theorem source_phase_3_3 : ∀ k : Fin 24, canonicalCoefficient 3 3 k = Scalar.mul (core 10) (phase 14) k := by
  decide +kernel

theorem source_phase_3_4 : ∀ k : Fin 24, canonicalCoefficient 3 4 k = Scalar.mul (core 9) (phase 10) k := by
  decide +kernel

theorem source_phase_3_5 : ∀ k : Fin 24, canonicalCoefficient 3 5 k = Scalar.mul (core 2) (phase 18) k := by
  decide +kernel

theorem source_phase_3_6 : ∀ k : Fin 24, canonicalCoefficient 3 6 k = Scalar.mul (core 9) (phase 4) k := by
  decide +kernel

theorem source_phase_3_7 : ∀ k : Fin 24, canonicalCoefficient 3 7 k = Scalar.mul (core 2) (phase 8) k := by
  decide +kernel

theorem source_phase_3_8 : ∀ k : Fin 24, canonicalCoefficient 3 8 k = Scalar.mul (core 10) (phase 14) k := by
  decide +kernel

theorem source_phase_3_9 : ∀ k : Fin 24, canonicalCoefficient 3 9 k = Scalar.mul (core 10) (phase 8) k := by
  decide +kernel

theorem source_phase_3_10 : ∀ k : Fin 24, canonicalCoefficient 3 10 k = Scalar.mul (core 2) (phase 14) k := by
  decide +kernel

theorem source_phase_3_11 : ∀ k : Fin 24, canonicalCoefficient 3 11 k = Scalar.mul (core 9) (phase 18) k := by
  decide +kernel

theorem gram_pair_41 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 2) k = gramPair 41 k := by
  decide +kernel

theorem gram_weight_41 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 3) (gramPair 41) k = gram 41 k := by
  decide +kernel

theorem gram_pair_42 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 9) k = gramPair 42 k := by
  decide +kernel

theorem gram_weight_42 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 3) (gramPair 42) k = gram 42 k := by
  decide +kernel

theorem gram_pair_43 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 10) k = gramPair 43 k := by
  decide +kernel

theorem gram_weight_43 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 3) (gramPair 43) k = gram 43 k := by
  decide +kernel

theorem gram_pair_44 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 9)) (core 2) k = gramPair 44 k := by
  decide +kernel

theorem gram_weight_44 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 3) (gramPair 44) k = gram 44 k := by
  decide +kernel

theorem gram_pair_45 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 9)) (core 9) k = gramPair 45 k := by
  decide +kernel

theorem gram_weight_45 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 3) (gramPair 45) k = gram 45 k := by
  decide +kernel

theorem gram_pair_46 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 9)) (core 10) k = gramPair 46 k := by
  decide +kernel

theorem gram_weight_46 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 3) (gramPair 46) k = gram 46 k := by
  decide +kernel

theorem gram_pair_47 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 10)) (core 2) k = gramPair 47 k := by
  decide +kernel

theorem gram_weight_47 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 3) (gramPair 47) k = gram 47 k := by
  decide +kernel

theorem gram_pair_48 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 10)) (core 9) k = gramPair 48 k := by
  decide +kernel

theorem gram_weight_48 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 3) (gramPair 48) k = gram 48 k := by
  decide +kernel

theorem gram_pair_49 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 10)) (core 10) k = gramPair 49 k := by
  decide +kernel

theorem gram_weight_49 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 3) (gramPair 49) k = gram 49 k := by
  decide +kernel


end CGLMP5.SOSFinite
