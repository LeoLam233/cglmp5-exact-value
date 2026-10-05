import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear16
import CGLMP5.SOSPhaseLinear17

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_6_0 : commonDenominator 6 / (gramDenominator 67 * phaseDenominator 17) = 1 := by
  decide +kernel

private theorem scale_6_1 : commonDenominator 6 / (gramDenominator 96 * phaseDenominator 16) = 2 := by
  decide +kernel

theorem denominator_divides_006 : ∀ f ∈ fiber 6, commonDenominator 6 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_6_0 : integerCoordinateClaim 6 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_0, phase_linear_17_0, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_1 : integerCoordinateClaim 6 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_1, phase_linear_17_1, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_2 : integerCoordinateClaim 6 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_2, phase_linear_17_2, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_3 : integerCoordinateClaim 6 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_3, phase_linear_17_3, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_4 : integerCoordinateClaim 6 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_4, phase_linear_17_4, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_5 : integerCoordinateClaim 6 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_5, phase_linear_17_5, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_6 : integerCoordinateClaim 6 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_6, phase_linear_17_6, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_7 : integerCoordinateClaim 6 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_7, phase_linear_17_7, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_8 : integerCoordinateClaim 6 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_8, phase_linear_17_8, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_9 : integerCoordinateClaim 6 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_9, phase_linear_17_9, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_10 : integerCoordinateClaim 6 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_10, phase_linear_17_10, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_11 : integerCoordinateClaim 6 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_11, phase_linear_17_11, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_12 : integerCoordinateClaim 6 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_12, phase_linear_17_12, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_13 : integerCoordinateClaim 6 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_13, phase_linear_17_13, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_14 : integerCoordinateClaim 6 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_14, phase_linear_17_14, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_15 : integerCoordinateClaim 6 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_15, phase_linear_17_15, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_16 : integerCoordinateClaim 6 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_16, phase_linear_17_16, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_17 : integerCoordinateClaim 6 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_17, phase_linear_17_17, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_18 : integerCoordinateClaim 6 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_18, phase_linear_17_18, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_19 : integerCoordinateClaim 6 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_19, phase_linear_17_19, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_20 : integerCoordinateClaim 6 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_20, phase_linear_17_20, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_21 : integerCoordinateClaim 6 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_21, phase_linear_17_21, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_22 : integerCoordinateClaim 6 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_22, phase_linear_17_22, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

private theorem coordinate_6_23 : integerCoordinateClaim 6 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_6_0, scale_6_1, phase_linear_16_23, phase_linear_17_23, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_6, target_denominator_literal_6, target_numerator_literal_6]
  decide +kernel

theorem integer_residual_006 : integerResidualClaim 6 :=
  (Fin.cases coordinate_6_0 (Fin.cases coordinate_6_1 (Fin.cases coordinate_6_2 (Fin.cases coordinate_6_3 (Fin.cases coordinate_6_4 (Fin.cases coordinate_6_5 (Fin.cases coordinate_6_6 (Fin.cases coordinate_6_7 (Fin.cases coordinate_6_8 (Fin.cases coordinate_6_9 (Fin.cases coordinate_6_10 (Fin.cases coordinate_6_11 (Fin.cases coordinate_6_12 (Fin.cases coordinate_6_13 (Fin.cases coordinate_6_14 (Fin.cases coordinate_6_15 (Fin.cases coordinate_6_16 (Fin.cases coordinate_6_17 (Fin.cases coordinate_6_18 (Fin.cases coordinate_6_19 (Fin.cases coordinate_6_20 (Fin.cases coordinate_6_21 (Fin.cases coordinate_6_22 (Fin.cases coordinate_6_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
