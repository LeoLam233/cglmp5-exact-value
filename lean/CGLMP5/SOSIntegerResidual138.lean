import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear00
import CGLMP5.SOSPhaseLinear10

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_138_0 : commonDenominator 138 / (gramDenominator 63 * phaseDenominator 10) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_138_1 : commonDenominator 138 / (gramDenominator 98 * phaseDenominator 0) = 1 := by
  decide +kernel

private theorem scale_138_2 : commonDenominator 138 / (gramDenominator 106 * phaseDenominator 0) = 1 := by
  decide +kernel

theorem denominator_divides_138 : ∀ f ∈ fiber 138, commonDenominator 138 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_138_0 : integerCoordinateClaim 138 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_0, phase_linear_10_0, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_1 : integerCoordinateClaim 138 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_1, phase_linear_10_1, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_2 : integerCoordinateClaim 138 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_2, phase_linear_10_2, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_3 : integerCoordinateClaim 138 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_3, phase_linear_10_3, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_4 : integerCoordinateClaim 138 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_4, phase_linear_10_4, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_5 : integerCoordinateClaim 138 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_5, phase_linear_10_5, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_6 : integerCoordinateClaim 138 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_6, phase_linear_10_6, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_7 : integerCoordinateClaim 138 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_7, phase_linear_10_7, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_8 : integerCoordinateClaim 138 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_8, phase_linear_10_8, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_9 : integerCoordinateClaim 138 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_9, phase_linear_10_9, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_10 : integerCoordinateClaim 138 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_10, phase_linear_10_10, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_11 : integerCoordinateClaim 138 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_11, phase_linear_10_11, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_12 : integerCoordinateClaim 138 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_12, phase_linear_10_12, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_13 : integerCoordinateClaim 138 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_13, phase_linear_10_13, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_14 : integerCoordinateClaim 138 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_14, phase_linear_10_14, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_15 : integerCoordinateClaim 138 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_15, phase_linear_10_15, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_16 : integerCoordinateClaim 138 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_16, phase_linear_10_16, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_17 : integerCoordinateClaim 138 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_17, phase_linear_10_17, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_18 : integerCoordinateClaim 138 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_18, phase_linear_10_18, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_19 : integerCoordinateClaim 138 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_19, phase_linear_10_19, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_20 : integerCoordinateClaim 138 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_20, phase_linear_10_20, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_21 : integerCoordinateClaim 138 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_21, phase_linear_10_21, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_22 : integerCoordinateClaim 138 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_22, phase_linear_10_22, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

private theorem coordinate_138_23 : integerCoordinateClaim 138 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_138]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_138_0, scale_138_1, scale_138_2, phase_linear_0_23, phase_linear_10_23, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_138, target_denominator_literal_138, target_numerator_literal_138]
  decide +kernel

theorem integer_residual_138 : integerResidualClaim 138 :=
  (Fin.cases coordinate_138_0 (Fin.cases coordinate_138_1 (Fin.cases coordinate_138_2 (Fin.cases coordinate_138_3 (Fin.cases coordinate_138_4 (Fin.cases coordinate_138_5 (Fin.cases coordinate_138_6 (Fin.cases coordinate_138_7 (Fin.cases coordinate_138_8 (Fin.cases coordinate_138_9 (Fin.cases coordinate_138_10 (Fin.cases coordinate_138_11 (Fin.cases coordinate_138_12 (Fin.cases coordinate_138_13 (Fin.cases coordinate_138_14 (Fin.cases coordinate_138_15 (Fin.cases coordinate_138_16 (Fin.cases coordinate_138_17 (Fin.cases coordinate_138_18 (Fin.cases coordinate_138_19 (Fin.cases coordinate_138_20 (Fin.cases coordinate_138_21 (Fin.cases coordinate_138_22 (Fin.cases coordinate_138_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
