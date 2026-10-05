import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear00
import CGLMP5.SOSPhaseLinear01

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_14_0 : commonDenominator 14 / (gramDenominator 67 * phaseDenominator 1) = 1 := by
  decide +kernel

private theorem scale_14_1 : commonDenominator 14 / (gramDenominator 96 * phaseDenominator 0) = 4 := by
  decide +kernel

theorem denominator_divides_014 : ∀ f ∈ fiber 14, commonDenominator 14 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_14_0 : integerCoordinateClaim 14 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_0, phase_linear_1_0, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_1 : integerCoordinateClaim 14 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_1, phase_linear_1_1, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_2 : integerCoordinateClaim 14 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_2, phase_linear_1_2, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_3 : integerCoordinateClaim 14 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_3, phase_linear_1_3, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_4 : integerCoordinateClaim 14 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_4, phase_linear_1_4, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_5 : integerCoordinateClaim 14 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_5, phase_linear_1_5, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_6 : integerCoordinateClaim 14 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_6, phase_linear_1_6, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_7 : integerCoordinateClaim 14 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_7, phase_linear_1_7, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_8 : integerCoordinateClaim 14 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_8, phase_linear_1_8, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_9 : integerCoordinateClaim 14 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_9, phase_linear_1_9, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_10 : integerCoordinateClaim 14 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_10, phase_linear_1_10, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_11 : integerCoordinateClaim 14 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_11, phase_linear_1_11, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_12 : integerCoordinateClaim 14 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_12, phase_linear_1_12, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_13 : integerCoordinateClaim 14 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_13, phase_linear_1_13, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_14 : integerCoordinateClaim 14 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_14, phase_linear_1_14, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_15 : integerCoordinateClaim 14 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_15, phase_linear_1_15, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_16 : integerCoordinateClaim 14 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_16, phase_linear_1_16, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_17 : integerCoordinateClaim 14 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_17, phase_linear_1_17, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_18 : integerCoordinateClaim 14 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_18, phase_linear_1_18, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_19 : integerCoordinateClaim 14 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_19, phase_linear_1_19, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_20 : integerCoordinateClaim 14 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_20, phase_linear_1_20, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_21 : integerCoordinateClaim 14 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_21, phase_linear_1_21, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_22 : integerCoordinateClaim 14 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_22, phase_linear_1_22, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

private theorem coordinate_14_23 : integerCoordinateClaim 14 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_14]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_14_0, scale_14_1, phase_linear_0_23, phase_linear_1_23, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_14, target_denominator_literal_14, target_numerator_literal_14]
  decide +kernel

theorem integer_residual_014 : integerResidualClaim 14 :=
  (Fin.cases coordinate_14_0 (Fin.cases coordinate_14_1 (Fin.cases coordinate_14_2 (Fin.cases coordinate_14_3 (Fin.cases coordinate_14_4 (Fin.cases coordinate_14_5 (Fin.cases coordinate_14_6 (Fin.cases coordinate_14_7 (Fin.cases coordinate_14_8 (Fin.cases coordinate_14_9 (Fin.cases coordinate_14_10 (Fin.cases coordinate_14_11 (Fin.cases coordinate_14_12 (Fin.cases coordinate_14_13 (Fin.cases coordinate_14_14 (Fin.cases coordinate_14_15 (Fin.cases coordinate_14_16 (Fin.cases coordinate_14_17 (Fin.cases coordinate_14_18 (Fin.cases coordinate_14_19 (Fin.cases coordinate_14_20 (Fin.cases coordinate_14_21 (Fin.cases coordinate_14_22 (Fin.cases coordinate_14_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
