import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear00
import CGLMP5.SOSPhaseLinear01

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_170_0 : commonDenominator 170 / (gramDenominator 67 * phaseDenominator 1) = 1 := by
  decide +kernel

private theorem scale_170_1 : commonDenominator 170 / (gramDenominator 96 * phaseDenominator 0) = 4 := by
  decide +kernel

theorem denominator_divides_170 : ∀ f ∈ fiber 170, commonDenominator 170 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_170_0 : integerCoordinateClaim 170 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_0, phase_linear_1_0, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_1 : integerCoordinateClaim 170 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_1, phase_linear_1_1, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_2 : integerCoordinateClaim 170 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_2, phase_linear_1_2, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_3 : integerCoordinateClaim 170 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_3, phase_linear_1_3, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_4 : integerCoordinateClaim 170 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_4, phase_linear_1_4, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_5 : integerCoordinateClaim 170 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_5, phase_linear_1_5, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_6 : integerCoordinateClaim 170 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_6, phase_linear_1_6, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_7 : integerCoordinateClaim 170 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_7, phase_linear_1_7, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_8 : integerCoordinateClaim 170 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_8, phase_linear_1_8, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_9 : integerCoordinateClaim 170 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_9, phase_linear_1_9, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_10 : integerCoordinateClaim 170 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_10, phase_linear_1_10, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_11 : integerCoordinateClaim 170 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_11, phase_linear_1_11, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_12 : integerCoordinateClaim 170 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_12, phase_linear_1_12, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_13 : integerCoordinateClaim 170 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_13, phase_linear_1_13, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_14 : integerCoordinateClaim 170 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_14, phase_linear_1_14, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_15 : integerCoordinateClaim 170 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_15, phase_linear_1_15, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_16 : integerCoordinateClaim 170 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_16, phase_linear_1_16, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_17 : integerCoordinateClaim 170 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_17, phase_linear_1_17, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_18 : integerCoordinateClaim 170 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_18, phase_linear_1_18, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_19 : integerCoordinateClaim 170 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_19, phase_linear_1_19, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_20 : integerCoordinateClaim 170 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_20, phase_linear_1_20, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_21 : integerCoordinateClaim 170 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_21, phase_linear_1_21, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_22 : integerCoordinateClaim 170 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_22, phase_linear_1_22, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

private theorem coordinate_170_23 : integerCoordinateClaim 170 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_170]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_170_0, scale_170_1, phase_linear_0_23, phase_linear_1_23, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_170, target_denominator_literal_170, target_numerator_literal_170]
  decide +kernel

theorem integer_residual_170 : integerResidualClaim 170 :=
  (Fin.cases coordinate_170_0 (Fin.cases coordinate_170_1 (Fin.cases coordinate_170_2 (Fin.cases coordinate_170_3 (Fin.cases coordinate_170_4 (Fin.cases coordinate_170_5 (Fin.cases coordinate_170_6 (Fin.cases coordinate_170_7 (Fin.cases coordinate_170_8 (Fin.cases coordinate_170_9 (Fin.cases coordinate_170_10 (Fin.cases coordinate_170_11 (Fin.cases coordinate_170_12 (Fin.cases coordinate_170_13 (Fin.cases coordinate_170_14 (Fin.cases coordinate_170_15 (Fin.cases coordinate_170_16 (Fin.cases coordinate_170_17 (Fin.cases coordinate_170_18 (Fin.cases coordinate_170_19 (Fin.cases coordinate_170_20 (Fin.cases coordinate_170_21 (Fin.cases coordinate_170_22 (Fin.cases coordinate_170_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
