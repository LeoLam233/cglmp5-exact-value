import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear12
import CGLMP5.SOSPhaseLinear13

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_41_0 : commonDenominator 41 / (gramDenominator 67 * phaseDenominator 13) = 1 := by
  decide +kernel

private theorem scale_41_1 : commonDenominator 41 / (gramDenominator 96 * phaseDenominator 12) = 1 := by
  decide +kernel

theorem denominator_divides_041 : ∀ f ∈ fiber 41, commonDenominator 41 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_41_0 : integerCoordinateClaim 41 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_0, phase_linear_13_0, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_1 : integerCoordinateClaim 41 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_1, phase_linear_13_1, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_2 : integerCoordinateClaim 41 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_2, phase_linear_13_2, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_3 : integerCoordinateClaim 41 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_3, phase_linear_13_3, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_4 : integerCoordinateClaim 41 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_4, phase_linear_13_4, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_5 : integerCoordinateClaim 41 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_5, phase_linear_13_5, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_6 : integerCoordinateClaim 41 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_6, phase_linear_13_6, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_7 : integerCoordinateClaim 41 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_7, phase_linear_13_7, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_8 : integerCoordinateClaim 41 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_8, phase_linear_13_8, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_9 : integerCoordinateClaim 41 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_9, phase_linear_13_9, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_10 : integerCoordinateClaim 41 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_10, phase_linear_13_10, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_11 : integerCoordinateClaim 41 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_11, phase_linear_13_11, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_12 : integerCoordinateClaim 41 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_12, phase_linear_13_12, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_13 : integerCoordinateClaim 41 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_13, phase_linear_13_13, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_14 : integerCoordinateClaim 41 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_14, phase_linear_13_14, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_15 : integerCoordinateClaim 41 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_15, phase_linear_13_15, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_16 : integerCoordinateClaim 41 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_16, phase_linear_13_16, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_17 : integerCoordinateClaim 41 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_17, phase_linear_13_17, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_18 : integerCoordinateClaim 41 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_18, phase_linear_13_18, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_19 : integerCoordinateClaim 41 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_19, phase_linear_13_19, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_20 : integerCoordinateClaim 41 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_20, phase_linear_13_20, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_21 : integerCoordinateClaim 41 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_21, phase_linear_13_21, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_22 : integerCoordinateClaim 41 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_22, phase_linear_13_22, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

private theorem coordinate_41_23 : integerCoordinateClaim 41 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_41]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_41_0, scale_41_1, phase_linear_12_23, phase_linear_13_23, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_41, target_denominator_literal_41, target_numerator_literal_41]
  decide +kernel

theorem integer_residual_041 : integerResidualClaim 41 :=
  (Fin.cases coordinate_41_0 (Fin.cases coordinate_41_1 (Fin.cases coordinate_41_2 (Fin.cases coordinate_41_3 (Fin.cases coordinate_41_4 (Fin.cases coordinate_41_5 (Fin.cases coordinate_41_6 (Fin.cases coordinate_41_7 (Fin.cases coordinate_41_8 (Fin.cases coordinate_41_9 (Fin.cases coordinate_41_10 (Fin.cases coordinate_41_11 (Fin.cases coordinate_41_12 (Fin.cases coordinate_41_13 (Fin.cases coordinate_41_14 (Fin.cases coordinate_41_15 (Fin.cases coordinate_41_16 (Fin.cases coordinate_41_17 (Fin.cases coordinate_41_18 (Fin.cases coordinate_41_19 (Fin.cases coordinate_41_20 (Fin.cases coordinate_41_21 (Fin.cases coordinate_41_22 (Fin.cases coordinate_41_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
