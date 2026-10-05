import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear00
import CGLMP5.SOSPhaseLinear10

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_128_0 : commonDenominator 128 / (gramDenominator 57 * phaseDenominator 10) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_128_1 : commonDenominator 128 / (gramDenominator 95 * phaseDenominator 0) = 1 := by
  decide +kernel

private theorem scale_128_2 : commonDenominator 128 / (gramDenominator 102 * phaseDenominator 0) = 1 := by
  decide +kernel

theorem denominator_divides_128 : ∀ f ∈ fiber 128, commonDenominator 128 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_128_0 : integerCoordinateClaim 128 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_0, phase_linear_10_0, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_1 : integerCoordinateClaim 128 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_1, phase_linear_10_1, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_2 : integerCoordinateClaim 128 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_2, phase_linear_10_2, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_3 : integerCoordinateClaim 128 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_3, phase_linear_10_3, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_4 : integerCoordinateClaim 128 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_4, phase_linear_10_4, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_5 : integerCoordinateClaim 128 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_5, phase_linear_10_5, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_6 : integerCoordinateClaim 128 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_6, phase_linear_10_6, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_7 : integerCoordinateClaim 128 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_7, phase_linear_10_7, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_8 : integerCoordinateClaim 128 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_8, phase_linear_10_8, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_9 : integerCoordinateClaim 128 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_9, phase_linear_10_9, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_10 : integerCoordinateClaim 128 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_10, phase_linear_10_10, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_11 : integerCoordinateClaim 128 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_11, phase_linear_10_11, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_12 : integerCoordinateClaim 128 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_12, phase_linear_10_12, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_13 : integerCoordinateClaim 128 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_13, phase_linear_10_13, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_14 : integerCoordinateClaim 128 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_14, phase_linear_10_14, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_15 : integerCoordinateClaim 128 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_15, phase_linear_10_15, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_16 : integerCoordinateClaim 128 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_16, phase_linear_10_16, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_17 : integerCoordinateClaim 128 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_17, phase_linear_10_17, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_18 : integerCoordinateClaim 128 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_18, phase_linear_10_18, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_19 : integerCoordinateClaim 128 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_19, phase_linear_10_19, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_20 : integerCoordinateClaim 128 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_20, phase_linear_10_20, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_21 : integerCoordinateClaim 128 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_21, phase_linear_10_21, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_22 : integerCoordinateClaim 128 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_22, phase_linear_10_22, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

private theorem coordinate_128_23 : integerCoordinateClaim 128 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_128]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_128_0, scale_128_1, scale_128_2, phase_linear_0_23, phase_linear_10_23, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_128, target_denominator_literal_128, target_numerator_literal_128]
  decide +kernel

theorem integer_residual_128 : integerResidualClaim 128 :=
  (Fin.cases coordinate_128_0 (Fin.cases coordinate_128_1 (Fin.cases coordinate_128_2 (Fin.cases coordinate_128_3 (Fin.cases coordinate_128_4 (Fin.cases coordinate_128_5 (Fin.cases coordinate_128_6 (Fin.cases coordinate_128_7 (Fin.cases coordinate_128_8 (Fin.cases coordinate_128_9 (Fin.cases coordinate_128_10 (Fin.cases coordinate_128_11 (Fin.cases coordinate_128_12 (Fin.cases coordinate_128_13 (Fin.cases coordinate_128_14 (Fin.cases coordinate_128_15 (Fin.cases coordinate_128_16 (Fin.cases coordinate_128_17 (Fin.cases coordinate_128_18 (Fin.cases coordinate_128_19 (Fin.cases coordinate_128_20 (Fin.cases coordinate_128_21 (Fin.cases coordinate_128_22 (Fin.cases coordinate_128_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
