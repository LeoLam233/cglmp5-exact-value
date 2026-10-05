import CGLMP5.SOSCompressedData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem source_phase_10_0 : ∀ k : Fin 24, canonicalCoefficient 10 0 k = core 21 k := by
  decide +kernel

theorem source_phase_10_1 : ∀ k : Fin 24, canonicalCoefficient 10 1 k = Scalar.mul (core 21) (phase 4) k := by
  decide +kernel

theorem source_phase_10_2 : ∀ k : Fin 24, canonicalCoefficient 10 2 k = core 2 k := by
  decide +kernel

theorem source_phase_10_3 : ∀ k : Fin 24, canonicalCoefficient 10 3 k = core 2 k := by
  decide +kernel

theorem source_phase_10_4 : ∀ k : Fin 24, canonicalCoefficient 10 4 k = Scalar.mul (core 21) (phase 8) k := by
  decide +kernel

theorem source_phase_10_5 : ∀ k : Fin 24, canonicalCoefficient 10 5 k = core 22 k := by
  decide +kernel

theorem source_phase_10_6 : ∀ k : Fin 24, canonicalCoefficient 10 6 k = Scalar.mul (core 22) (phase 12) k := by
  decide +kernel

theorem source_phase_10_7 : ∀ k : Fin 24, canonicalCoefficient 10 7 k = Scalar.mul (core 2) (phase 12) k := by
  decide +kernel

theorem source_phase_10_8 : ∀ k : Fin 24, canonicalCoefficient 10 8 k = Scalar.mul (core 2) (phase 4) k := by
  decide +kernel

theorem source_phase_10_9 : ∀ k : Fin 24, canonicalCoefficient 10 9 k = Scalar.mul (core 21) (phase 12) k := by
  decide +kernel

theorem source_phase_10_10 : ∀ k : Fin 24, canonicalCoefficient 10 10 k = Scalar.mul (core 22) (phase 12) k := by
  decide +kernel

theorem source_phase_10_11 : ∀ k : Fin 24, canonicalCoefficient 10 11 k = Scalar.mul (core 22) (phase 4) k := by
  decide +kernel

theorem gram_pair_100 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 2) k = gramPair 100 k := by
  decide +kernel

theorem gram_weight_100 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 10) (gramPair 100) k = gram 100 k := by
  decide +kernel

theorem gram_pair_101 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 21) k = gramPair 101 k := by
  decide +kernel

theorem gram_weight_101 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 10) (gramPair 101) k = gram 101 k := by
  decide +kernel

theorem gram_pair_102 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 2)) (core 22) k = gramPair 102 k := by
  decide +kernel

theorem gram_weight_102 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 10) (gramPair 102) k = gram 102 k := by
  decide +kernel

theorem gram_pair_103 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 21)) (core 2) k = gramPair 103 k := by
  decide +kernel

theorem gram_weight_103 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 10) (gramPair 103) k = gram 103 k := by
  decide +kernel

theorem gram_pair_104 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 21)) (core 21) k = gramPair 104 k := by
  decide +kernel

theorem gram_weight_104 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 10) (gramPair 104) k = gram 104 k := by
  decide +kernel

theorem gram_pair_105 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 21)) (core 22) k = gramPair 105 k := by
  decide +kernel

theorem gram_weight_105 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 10) (gramPair 105) k = gram 105 k := by
  decide +kernel

theorem gram_pair_106 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 22)) (core 2) k = gramPair 106 k := by
  decide +kernel

theorem gram_weight_106 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 10) (gramPair 106) k = gram 106 k := by
  decide +kernel

theorem gram_pair_107 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 22)) (core 21) k = gramPair 107 k := by
  decide +kernel

theorem gram_weight_107 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 10) (gramPair 107) k = gram 107 k := by
  decide +kernel

theorem gram_pair_108 : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core 22)) (core 22) k = gramPair 108 k := by
  decide +kernel

theorem gram_weight_108 : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight 10) (gramPair 108) k = gram 108 k := by
  decide +kernel


end CGLMP5.SOSFinite
