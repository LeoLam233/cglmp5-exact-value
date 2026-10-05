import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear02
import CGLMP5.SOSPhaseLinear12

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_127_0 : commonDenominator 127 / (gramDenominator 57 * phaseDenominator 2) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_127_1 : commonDenominator 127 / (gramDenominator 95 * phaseDenominator 12) = 1 := by
  decide +kernel

private theorem scale_127_2 : commonDenominator 127 / (gramDenominator 102 * phaseDenominator 12) = 1 := by
  decide +kernel

theorem denominator_divides_127 : ∀ f ∈ fiber 127, commonDenominator 127 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_127_0 : integerCoordinateClaim 127 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_0, phase_linear_12_0, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_1 : integerCoordinateClaim 127 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_1, phase_linear_12_1, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_2 : integerCoordinateClaim 127 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_2, phase_linear_12_2, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_3 : integerCoordinateClaim 127 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_3, phase_linear_12_3, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_4 : integerCoordinateClaim 127 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_4, phase_linear_12_4, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_5 : integerCoordinateClaim 127 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_5, phase_linear_12_5, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_6 : integerCoordinateClaim 127 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_6, phase_linear_12_6, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_7 : integerCoordinateClaim 127 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_7, phase_linear_12_7, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_8 : integerCoordinateClaim 127 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_8, phase_linear_12_8, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_9 : integerCoordinateClaim 127 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_9, phase_linear_12_9, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_10 : integerCoordinateClaim 127 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_10, phase_linear_12_10, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_11 : integerCoordinateClaim 127 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_11, phase_linear_12_11, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_12 : integerCoordinateClaim 127 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_12, phase_linear_12_12, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_13 : integerCoordinateClaim 127 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_13, phase_linear_12_13, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_14 : integerCoordinateClaim 127 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_14, phase_linear_12_14, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_15 : integerCoordinateClaim 127 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_15, phase_linear_12_15, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_16 : integerCoordinateClaim 127 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_16, phase_linear_12_16, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_17 : integerCoordinateClaim 127 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_17, phase_linear_12_17, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_18 : integerCoordinateClaim 127 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_18, phase_linear_12_18, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_19 : integerCoordinateClaim 127 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_19, phase_linear_12_19, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_20 : integerCoordinateClaim 127 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_20, phase_linear_12_20, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_21 : integerCoordinateClaim 127 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_21, phase_linear_12_21, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_22 : integerCoordinateClaim 127 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_22, phase_linear_12_22, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

private theorem coordinate_127_23 : integerCoordinateClaim 127 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_127]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_127_0, scale_127_1, scale_127_2, phase_linear_2_23, phase_linear_12_23, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_127, target_denominator_literal_127, target_numerator_literal_127]
  decide +kernel

theorem integer_residual_127 : integerResidualClaim 127 :=
  (Fin.cases coordinate_127_0 (Fin.cases coordinate_127_1 (Fin.cases coordinate_127_2 (Fin.cases coordinate_127_3 (Fin.cases coordinate_127_4 (Fin.cases coordinate_127_5 (Fin.cases coordinate_127_6 (Fin.cases coordinate_127_7 (Fin.cases coordinate_127_8 (Fin.cases coordinate_127_9 (Fin.cases coordinate_127_10 (Fin.cases coordinate_127_11 (Fin.cases coordinate_127_12 (Fin.cases coordinate_127_13 (Fin.cases coordinate_127_14 (Fin.cases coordinate_127_15 (Fin.cases coordinate_127_16 (Fin.cases coordinate_127_17 (Fin.cases coordinate_127_18 (Fin.cases coordinate_127_19 (Fin.cases coordinate_127_20 (Fin.cases coordinate_127_21 (Fin.cases coordinate_127_22 (Fin.cases coordinate_127_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
