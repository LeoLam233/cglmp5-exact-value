import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear00
import CGLMP5.SOSPhaseLinear10

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_8_0 : commonDenominator 8 / (gramDenominator 63 * phaseDenominator 10) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_8_1 : commonDenominator 8 / (gramDenominator 98 * phaseDenominator 0) = 1 := by
  decide +kernel

private theorem scale_8_2 : commonDenominator 8 / (gramDenominator 106 * phaseDenominator 0) = 1 := by
  decide +kernel

theorem denominator_divides_008 : ∀ f ∈ fiber 8, commonDenominator 8 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_8_0 : integerCoordinateClaim 8 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_0, phase_linear_10_0, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_1 : integerCoordinateClaim 8 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_1, phase_linear_10_1, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_2 : integerCoordinateClaim 8 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_2, phase_linear_10_2, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_3 : integerCoordinateClaim 8 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_3, phase_linear_10_3, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_4 : integerCoordinateClaim 8 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_4, phase_linear_10_4, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_5 : integerCoordinateClaim 8 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_5, phase_linear_10_5, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_6 : integerCoordinateClaim 8 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_6, phase_linear_10_6, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_7 : integerCoordinateClaim 8 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_7, phase_linear_10_7, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_8 : integerCoordinateClaim 8 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_8, phase_linear_10_8, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_9 : integerCoordinateClaim 8 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_9, phase_linear_10_9, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_10 : integerCoordinateClaim 8 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_10, phase_linear_10_10, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_11 : integerCoordinateClaim 8 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_11, phase_linear_10_11, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_12 : integerCoordinateClaim 8 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_12, phase_linear_10_12, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_13 : integerCoordinateClaim 8 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_13, phase_linear_10_13, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_14 : integerCoordinateClaim 8 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_14, phase_linear_10_14, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_15 : integerCoordinateClaim 8 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_15, phase_linear_10_15, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_16 : integerCoordinateClaim 8 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_16, phase_linear_10_16, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_17 : integerCoordinateClaim 8 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_17, phase_linear_10_17, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_18 : integerCoordinateClaim 8 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_18, phase_linear_10_18, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_19 : integerCoordinateClaim 8 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_19, phase_linear_10_19, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_20 : integerCoordinateClaim 8 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_20, phase_linear_10_20, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_21 : integerCoordinateClaim 8 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_21, phase_linear_10_21, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_22 : integerCoordinateClaim 8 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_22, phase_linear_10_22, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

private theorem coordinate_8_23 : integerCoordinateClaim 8 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_8_0, scale_8_1, scale_8_2, phase_linear_0_23, phase_linear_10_23, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_8, target_denominator_literal_8, target_numerator_literal_8]
  decide +kernel

theorem integer_residual_008 : integerResidualClaim 8 :=
  (Fin.cases coordinate_8_0 (Fin.cases coordinate_8_1 (Fin.cases coordinate_8_2 (Fin.cases coordinate_8_3 (Fin.cases coordinate_8_4 (Fin.cases coordinate_8_5 (Fin.cases coordinate_8_6 (Fin.cases coordinate_8_7 (Fin.cases coordinate_8_8 (Fin.cases coordinate_8_9 (Fin.cases coordinate_8_10 (Fin.cases coordinate_8_11 (Fin.cases coordinate_8_12 (Fin.cases coordinate_8_13 (Fin.cases coordinate_8_14 (Fin.cases coordinate_8_15 (Fin.cases coordinate_8_16 (Fin.cases coordinate_8_17 (Fin.cases coordinate_8_18 (Fin.cases coordinate_8_19 (Fin.cases coordinate_8_20 (Fin.cases coordinate_8_21 (Fin.cases coordinate_8_22 (Fin.cases coordinate_8_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
