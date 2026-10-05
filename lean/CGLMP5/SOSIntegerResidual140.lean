import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear16
import CGLMP5.SOSPhaseLinear17

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_140_0 : commonDenominator 140 / (gramDenominator 67 * phaseDenominator 17) = 1 := by
  decide +kernel

private theorem scale_140_1 : commonDenominator 140 / (gramDenominator 96 * phaseDenominator 16) = 2 := by
  decide +kernel

theorem denominator_divides_140 : ∀ f ∈ fiber 140, commonDenominator 140 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_140_0 : integerCoordinateClaim 140 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_0, phase_linear_17_0, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_1 : integerCoordinateClaim 140 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_1, phase_linear_17_1, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_2 : integerCoordinateClaim 140 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_2, phase_linear_17_2, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_3 : integerCoordinateClaim 140 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_3, phase_linear_17_3, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_4 : integerCoordinateClaim 140 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_4, phase_linear_17_4, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_5 : integerCoordinateClaim 140 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_5, phase_linear_17_5, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_6 : integerCoordinateClaim 140 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_6, phase_linear_17_6, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_7 : integerCoordinateClaim 140 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_7, phase_linear_17_7, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_8 : integerCoordinateClaim 140 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_8, phase_linear_17_8, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_9 : integerCoordinateClaim 140 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_9, phase_linear_17_9, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_10 : integerCoordinateClaim 140 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_10, phase_linear_17_10, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_11 : integerCoordinateClaim 140 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_11, phase_linear_17_11, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_12 : integerCoordinateClaim 140 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_12, phase_linear_17_12, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_13 : integerCoordinateClaim 140 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_13, phase_linear_17_13, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_14 : integerCoordinateClaim 140 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_14, phase_linear_17_14, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_15 : integerCoordinateClaim 140 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_15, phase_linear_17_15, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_16 : integerCoordinateClaim 140 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_16, phase_linear_17_16, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_17 : integerCoordinateClaim 140 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_17, phase_linear_17_17, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_18 : integerCoordinateClaim 140 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_18, phase_linear_17_18, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_19 : integerCoordinateClaim 140 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_19, phase_linear_17_19, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_20 : integerCoordinateClaim 140 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_20, phase_linear_17_20, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_21 : integerCoordinateClaim 140 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_21, phase_linear_17_21, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_22 : integerCoordinateClaim 140 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_22, phase_linear_17_22, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

private theorem coordinate_140_23 : integerCoordinateClaim 140 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_140]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_140_0, scale_140_1, phase_linear_16_23, phase_linear_17_23, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_140, target_denominator_literal_140, target_numerator_literal_140]
  decide +kernel

theorem integer_residual_140 : integerResidualClaim 140 :=
  (Fin.cases coordinate_140_0 (Fin.cases coordinate_140_1 (Fin.cases coordinate_140_2 (Fin.cases coordinate_140_3 (Fin.cases coordinate_140_4 (Fin.cases coordinate_140_5 (Fin.cases coordinate_140_6 (Fin.cases coordinate_140_7 (Fin.cases coordinate_140_8 (Fin.cases coordinate_140_9 (Fin.cases coordinate_140_10 (Fin.cases coordinate_140_11 (Fin.cases coordinate_140_12 (Fin.cases coordinate_140_13 (Fin.cases coordinate_140_14 (Fin.cases coordinate_140_15 (Fin.cases coordinate_140_16 (Fin.cases coordinate_140_17 (Fin.cases coordinate_140_18 (Fin.cases coordinate_140_19 (Fin.cases coordinate_140_20 (Fin.cases coordinate_140_21 (Fin.cases coordinate_140_22 (Fin.cases coordinate_140_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
