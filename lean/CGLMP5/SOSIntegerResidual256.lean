import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear00
import CGLMP5.SOSPhaseLinear10

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_256_0 : commonDenominator 256 / (gramDenominator 57 * phaseDenominator 10) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_256_1 : commonDenominator 256 / (gramDenominator 95 * phaseDenominator 0) = 1 := by
  decide +kernel

private theorem scale_256_2 : commonDenominator 256 / (gramDenominator 102 * phaseDenominator 0) = 1 := by
  decide +kernel

theorem denominator_divides_256 : ∀ f ∈ fiber 256, commonDenominator 256 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_256_0 : integerCoordinateClaim 256 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_0, phase_linear_10_0, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_1 : integerCoordinateClaim 256 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_1, phase_linear_10_1, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_2 : integerCoordinateClaim 256 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_2, phase_linear_10_2, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_3 : integerCoordinateClaim 256 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_3, phase_linear_10_3, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_4 : integerCoordinateClaim 256 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_4, phase_linear_10_4, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_5 : integerCoordinateClaim 256 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_5, phase_linear_10_5, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_6 : integerCoordinateClaim 256 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_6, phase_linear_10_6, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_7 : integerCoordinateClaim 256 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_7, phase_linear_10_7, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_8 : integerCoordinateClaim 256 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_8, phase_linear_10_8, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_9 : integerCoordinateClaim 256 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_9, phase_linear_10_9, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_10 : integerCoordinateClaim 256 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_10, phase_linear_10_10, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_11 : integerCoordinateClaim 256 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_11, phase_linear_10_11, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_12 : integerCoordinateClaim 256 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_12, phase_linear_10_12, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_13 : integerCoordinateClaim 256 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_13, phase_linear_10_13, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_14 : integerCoordinateClaim 256 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_14, phase_linear_10_14, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_15 : integerCoordinateClaim 256 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_15, phase_linear_10_15, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_16 : integerCoordinateClaim 256 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_16, phase_linear_10_16, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_17 : integerCoordinateClaim 256 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_17, phase_linear_10_17, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_18 : integerCoordinateClaim 256 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_18, phase_linear_10_18, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_19 : integerCoordinateClaim 256 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_19, phase_linear_10_19, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_20 : integerCoordinateClaim 256 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_20, phase_linear_10_20, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_21 : integerCoordinateClaim 256 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_21, phase_linear_10_21, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_22 : integerCoordinateClaim 256 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_22, phase_linear_10_22, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

private theorem coordinate_256_23 : integerCoordinateClaim 256 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_256_0, scale_256_1, scale_256_2, phase_linear_0_23, phase_linear_10_23, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_256, target_denominator_literal_256, target_numerator_literal_256]
  decide +kernel

theorem integer_residual_256 : integerResidualClaim 256 :=
  (Fin.cases coordinate_256_0 (Fin.cases coordinate_256_1 (Fin.cases coordinate_256_2 (Fin.cases coordinate_256_3 (Fin.cases coordinate_256_4 (Fin.cases coordinate_256_5 (Fin.cases coordinate_256_6 (Fin.cases coordinate_256_7 (Fin.cases coordinate_256_8 (Fin.cases coordinate_256_9 (Fin.cases coordinate_256_10 (Fin.cases coordinate_256_11 (Fin.cases coordinate_256_12 (Fin.cases coordinate_256_13 (Fin.cases coordinate_256_14 (Fin.cases coordinate_256_15 (Fin.cases coordinate_256_16 (Fin.cases coordinate_256_17 (Fin.cases coordinate_256_18 (Fin.cases coordinate_256_19 (Fin.cases coordinate_256_20 (Fin.cases coordinate_256_21 (Fin.cases coordinate_256_22 (Fin.cases coordinate_256_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
