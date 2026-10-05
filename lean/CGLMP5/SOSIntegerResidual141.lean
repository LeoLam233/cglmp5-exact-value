import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear04
import CGLMP5.SOSPhaseLinear05

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_141_0 : commonDenominator 141 / (gramDenominator 67 * phaseDenominator 5) = 4 := by
  decide +kernel

private theorem scale_141_1 : commonDenominator 141 / (gramDenominator 96 * phaseDenominator 4) = 1 := by
  decide +kernel

theorem denominator_divides_141 : ∀ f ∈ fiber 141, commonDenominator 141 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_141_0 : integerCoordinateClaim 141 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_0, phase_linear_5_0, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_1 : integerCoordinateClaim 141 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_1, phase_linear_5_1, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_2 : integerCoordinateClaim 141 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_2, phase_linear_5_2, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_3 : integerCoordinateClaim 141 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_3, phase_linear_5_3, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_4 : integerCoordinateClaim 141 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_4, phase_linear_5_4, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_5 : integerCoordinateClaim 141 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_5, phase_linear_5_5, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_6 : integerCoordinateClaim 141 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_6, phase_linear_5_6, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_7 : integerCoordinateClaim 141 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_7, phase_linear_5_7, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_8 : integerCoordinateClaim 141 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_8, phase_linear_5_8, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_9 : integerCoordinateClaim 141 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_9, phase_linear_5_9, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_10 : integerCoordinateClaim 141 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_10, phase_linear_5_10, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_11 : integerCoordinateClaim 141 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_11, phase_linear_5_11, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_12 : integerCoordinateClaim 141 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_12, phase_linear_5_12, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_13 : integerCoordinateClaim 141 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_13, phase_linear_5_13, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_14 : integerCoordinateClaim 141 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_14, phase_linear_5_14, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_15 : integerCoordinateClaim 141 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_15, phase_linear_5_15, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_16 : integerCoordinateClaim 141 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_16, phase_linear_5_16, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_17 : integerCoordinateClaim 141 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_17, phase_linear_5_17, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_18 : integerCoordinateClaim 141 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_18, phase_linear_5_18, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_19 : integerCoordinateClaim 141 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_19, phase_linear_5_19, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_20 : integerCoordinateClaim 141 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_20, phase_linear_5_20, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_21 : integerCoordinateClaim 141 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_21, phase_linear_5_21, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_22 : integerCoordinateClaim 141 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_22, phase_linear_5_22, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

private theorem coordinate_141_23 : integerCoordinateClaim 141 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_141]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_141_0, scale_141_1, phase_linear_4_23, phase_linear_5_23, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_141, target_denominator_literal_141, target_numerator_literal_141]
  decide +kernel

theorem integer_residual_141 : integerResidualClaim 141 :=
  (Fin.cases coordinate_141_0 (Fin.cases coordinate_141_1 (Fin.cases coordinate_141_2 (Fin.cases coordinate_141_3 (Fin.cases coordinate_141_4 (Fin.cases coordinate_141_5 (Fin.cases coordinate_141_6 (Fin.cases coordinate_141_7 (Fin.cases coordinate_141_8 (Fin.cases coordinate_141_9 (Fin.cases coordinate_141_10 (Fin.cases coordinate_141_11 (Fin.cases coordinate_141_12 (Fin.cases coordinate_141_13 (Fin.cases coordinate_141_14 (Fin.cases coordinate_141_15 (Fin.cases coordinate_141_16 (Fin.cases coordinate_141_17 (Fin.cases coordinate_141_18 (Fin.cases coordinate_141_19 (Fin.cases coordinate_141_20 (Fin.cases coordinate_141_21 (Fin.cases coordinate_141_22 (Fin.cases coordinate_141_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
