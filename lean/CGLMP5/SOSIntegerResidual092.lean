import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear04
import CGLMP5.SOSPhaseLinear14

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_92_0 : commonDenominator 92 / (gramDenominator 57 * phaseDenominator 14) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_92_1 : commonDenominator 92 / (gramDenominator 95 * phaseDenominator 4) = 1 := by
  decide +kernel

private theorem scale_92_2 : commonDenominator 92 / (gramDenominator 102 * phaseDenominator 4) = 1 := by
  decide +kernel

theorem denominator_divides_092 : ∀ f ∈ fiber 92, commonDenominator 92 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_92_0 : integerCoordinateClaim 92 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_0, phase_linear_14_0, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_1 : integerCoordinateClaim 92 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_1, phase_linear_14_1, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_2 : integerCoordinateClaim 92 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_2, phase_linear_14_2, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_3 : integerCoordinateClaim 92 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_3, phase_linear_14_3, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_4 : integerCoordinateClaim 92 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_4, phase_linear_14_4, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_5 : integerCoordinateClaim 92 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_5, phase_linear_14_5, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_6 : integerCoordinateClaim 92 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_6, phase_linear_14_6, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_7 : integerCoordinateClaim 92 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_7, phase_linear_14_7, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_8 : integerCoordinateClaim 92 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_8, phase_linear_14_8, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_9 : integerCoordinateClaim 92 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_9, phase_linear_14_9, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_10 : integerCoordinateClaim 92 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_10, phase_linear_14_10, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_11 : integerCoordinateClaim 92 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_11, phase_linear_14_11, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_12 : integerCoordinateClaim 92 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_12, phase_linear_14_12, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_13 : integerCoordinateClaim 92 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_13, phase_linear_14_13, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_14 : integerCoordinateClaim 92 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_14, phase_linear_14_14, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_15 : integerCoordinateClaim 92 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_15, phase_linear_14_15, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_16 : integerCoordinateClaim 92 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_16, phase_linear_14_16, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_17 : integerCoordinateClaim 92 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_17, phase_linear_14_17, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_18 : integerCoordinateClaim 92 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_18, phase_linear_14_18, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_19 : integerCoordinateClaim 92 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_19, phase_linear_14_19, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_20 : integerCoordinateClaim 92 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_20, phase_linear_14_20, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_21 : integerCoordinateClaim 92 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_21, phase_linear_14_21, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_22 : integerCoordinateClaim 92 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_22, phase_linear_14_22, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

private theorem coordinate_92_23 : integerCoordinateClaim 92 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_92]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_92_0, scale_92_1, scale_92_2, phase_linear_4_23, phase_linear_14_23, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_92, target_denominator_literal_92, target_numerator_literal_92]
  decide +kernel

theorem integer_residual_092 : integerResidualClaim 92 :=
  (Fin.cases coordinate_92_0 (Fin.cases coordinate_92_1 (Fin.cases coordinate_92_2 (Fin.cases coordinate_92_3 (Fin.cases coordinate_92_4 (Fin.cases coordinate_92_5 (Fin.cases coordinate_92_6 (Fin.cases coordinate_92_7 (Fin.cases coordinate_92_8 (Fin.cases coordinate_92_9 (Fin.cases coordinate_92_10 (Fin.cases coordinate_92_11 (Fin.cases coordinate_92_12 (Fin.cases coordinate_92_13 (Fin.cases coordinate_92_14 (Fin.cases coordinate_92_15 (Fin.cases coordinate_92_16 (Fin.cases coordinate_92_17 (Fin.cases coordinate_92_18 (Fin.cases coordinate_92_19 (Fin.cases coordinate_92_20 (Fin.cases coordinate_92_21 (Fin.cases coordinate_92_22 (Fin.cases coordinate_92_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
