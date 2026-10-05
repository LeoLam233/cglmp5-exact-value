import CGLMP5.SOSCompressedData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem source_phase_7_0 : ∀ k : Fin 24, canonicalCoefficient 7 0 k = core 15 k := by
  decide +kernel

theorem source_phase_7_1 : ∀ k : Fin 24, canonicalCoefficient 7 1 k = Scalar.mul (core 15) (phase 6) k := by
  decide +kernel

theorem source_phase_7_2 : ∀ k : Fin 24, canonicalCoefficient 7 2 k = Scalar.mul (core 15) (phase 7) k := by
  decide +kernel

theorem source_phase_7_3 : ∀ k : Fin 24, canonicalCoefficient 7 3 k = core 2 k := by
  decide +kernel

theorem source_phase_7_4 : ∀ k : Fin 24, canonicalCoefficient 7 4 k = core 16 k := by
  decide +kernel

theorem source_phase_7_5 : ∀ k : Fin 24, canonicalCoefficient 7 5 k = Scalar.mul (core 16) (phase 9) k := by
  decide +kernel

theorem source_phase_7_6 : ∀ k : Fin 24, canonicalCoefficient 7 6 k = Scalar.mul (core 2) (phase 15) k := by
  decide +kernel

theorem source_phase_7_7 : ∀ k : Fin 24, canonicalCoefficient 7 7 k = Scalar.mul (core 15) (phase 13) k := by
  decide +kernel

theorem source_phase_7_8 : ∀ k : Fin 24, canonicalCoefficient 7 8 k = Scalar.mul (core 16) (phase 2) k := by
  decide +kernel

theorem source_phase_7_9 : ∀ k : Fin 24, canonicalCoefficient 7 9 k = Scalar.mul (core 2) (phase 6) k := by
  decide +kernel

theorem source_phase_7_10 : ∀ k : Fin 24, canonicalCoefficient 7 10 k = Scalar.mul (core 2) (phase 13) k := by
  decide +kernel

theorem source_phase_7_11 : ∀ k : Fin 24, canonicalCoefficient 7 11 k = Scalar.mul (core 16) (phase 15) k := by
  decide +kernel

theorem gram_pair_71 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 2) k = gramPair 71 k := by
  decide +kernel

theorem gram_weight_71 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 7) (gramPair 71) k = gram 71 k := by
  decide +kernel

theorem gram_pair_72 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 15) k = gramPair 72 k := by
  decide +kernel

theorem gram_weight_72 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 7) (gramPair 72) k = gram 72 k := by
  decide +kernel

theorem gram_pair_73 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 16) k = gramPair 73 k := by
  decide +kernel

theorem gram_weight_73 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 7) (gramPair 73) k = gram 73 k := by
  decide +kernel

theorem gram_pair_74 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 15)) (core 2) k = gramPair 74 k := by
  decide +kernel

theorem gram_weight_74 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 7) (gramPair 74) k = gram 74 k := by
  decide +kernel

theorem gram_pair_75 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 15)) (core 15) k = gramPair 75 k := by
  decide +kernel

theorem gram_weight_75 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 7) (gramPair 75) k = gram 75 k := by
  decide +kernel

theorem gram_pair_76 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 15)) (core 16) k = gramPair 76 k := by
  decide +kernel

theorem gram_weight_76 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 7) (gramPair 76) k = gram 76 k := by
  decide +kernel

theorem gram_pair_77 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 16)) (core 2) k = gramPair 77 k := by
  decide +kernel

theorem gram_weight_77 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 7) (gramPair 77) k = gram 77 k := by
  decide +kernel

theorem gram_pair_78 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 16)) (core 15) k = gramPair 78 k := by
  decide +kernel

theorem gram_weight_78 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 7) (gramPair 78) k = gram 78 k := by
  decide +kernel

theorem gram_pair_79 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 16)) (core 16) k = gramPair 79 k := by
  decide +kernel

theorem gram_weight_79 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 7) (gramPair 79) k = gram 79 k := by
  decide +kernel


end CGLMP5.SOSFinite
