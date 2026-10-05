import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear03
import CGLMP5.SOSPhaseLinear04

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_124_0 : commonDenominator 124 / (gramDenominator 58 * phaseDenominator 3) = 1 := by
  decide +kernel

private theorem scale_124_1 : commonDenominator 124 / (gramDenominator 87 * phaseDenominator 4) = 2 := by
  decide +kernel

theorem denominator_divides_124 : ∀ f ∈ fiber 124, commonDenominator 124 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_124_0 : integerCoordinateClaim 124 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_0, phase_linear_4_0, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_1 : integerCoordinateClaim 124 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_1, phase_linear_4_1, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_2 : integerCoordinateClaim 124 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_2, phase_linear_4_2, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_3 : integerCoordinateClaim 124 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_3, phase_linear_4_3, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_4 : integerCoordinateClaim 124 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_4, phase_linear_4_4, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_5 : integerCoordinateClaim 124 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_5, phase_linear_4_5, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_6 : integerCoordinateClaim 124 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_6, phase_linear_4_6, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_7 : integerCoordinateClaim 124 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_7, phase_linear_4_7, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_8 : integerCoordinateClaim 124 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_8, phase_linear_4_8, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_9 : integerCoordinateClaim 124 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_9, phase_linear_4_9, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_10 : integerCoordinateClaim 124 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_10, phase_linear_4_10, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_11 : integerCoordinateClaim 124 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_11, phase_linear_4_11, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_12 : integerCoordinateClaim 124 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_12, phase_linear_4_12, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_13 : integerCoordinateClaim 124 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_13, phase_linear_4_13, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_14 : integerCoordinateClaim 124 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_14, phase_linear_4_14, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_15 : integerCoordinateClaim 124 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_15, phase_linear_4_15, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_16 : integerCoordinateClaim 124 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_16, phase_linear_4_16, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_17 : integerCoordinateClaim 124 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_17, phase_linear_4_17, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_18 : integerCoordinateClaim 124 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_18, phase_linear_4_18, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_19 : integerCoordinateClaim 124 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_19, phase_linear_4_19, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_20 : integerCoordinateClaim 124 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_20, phase_linear_4_20, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_21 : integerCoordinateClaim 124 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_21, phase_linear_4_21, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_22 : integerCoordinateClaim 124 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_22, phase_linear_4_22, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

private theorem coordinate_124_23 : integerCoordinateClaim 124 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_124]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_124_0, scale_124_1, phase_linear_3_23, phase_linear_4_23, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_124, target_denominator_literal_124, target_numerator_literal_124]
  decide +kernel

theorem integer_residual_124 : integerResidualClaim 124 :=
  (Fin.cases coordinate_124_0 (Fin.cases coordinate_124_1 (Fin.cases coordinate_124_2 (Fin.cases coordinate_124_3 (Fin.cases coordinate_124_4 (Fin.cases coordinate_124_5 (Fin.cases coordinate_124_6 (Fin.cases coordinate_124_7 (Fin.cases coordinate_124_8 (Fin.cases coordinate_124_9 (Fin.cases coordinate_124_10 (Fin.cases coordinate_124_11 (Fin.cases coordinate_124_12 (Fin.cases coordinate_124_13 (Fin.cases coordinate_124_14 (Fin.cases coordinate_124_15 (Fin.cases coordinate_124_16 (Fin.cases coordinate_124_17 (Fin.cases coordinate_124_18 (Fin.cases coordinate_124_19 (Fin.cases coordinate_124_20 (Fin.cases coordinate_124_21 (Fin.cases coordinate_124_22 (Fin.cases coordinate_124_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
