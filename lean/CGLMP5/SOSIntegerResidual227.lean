import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear06
import CGLMP5.SOSPhaseLinear16

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_227_0 : commonDenominator 227 / (gramDenominator 57 * phaseDenominator 6) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_227_1 : commonDenominator 227 / (gramDenominator 95 * phaseDenominator 16) = 1 := by
  decide +kernel

private theorem scale_227_2 : commonDenominator 227 / (gramDenominator 102 * phaseDenominator 16) = 1 := by
  decide +kernel

theorem denominator_divides_227 : ∀ f ∈ fiber 227, commonDenominator 227 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_227_0 : integerCoordinateClaim 227 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_0, phase_linear_16_0, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_1 : integerCoordinateClaim 227 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_1, phase_linear_16_1, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_2 : integerCoordinateClaim 227 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_2, phase_linear_16_2, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_3 : integerCoordinateClaim 227 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_3, phase_linear_16_3, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_4 : integerCoordinateClaim 227 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_4, phase_linear_16_4, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_5 : integerCoordinateClaim 227 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_5, phase_linear_16_5, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_6 : integerCoordinateClaim 227 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_6, phase_linear_16_6, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_7 : integerCoordinateClaim 227 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_7, phase_linear_16_7, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_8 : integerCoordinateClaim 227 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_8, phase_linear_16_8, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_9 : integerCoordinateClaim 227 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_9, phase_linear_16_9, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_10 : integerCoordinateClaim 227 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_10, phase_linear_16_10, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_11 : integerCoordinateClaim 227 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_11, phase_linear_16_11, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_12 : integerCoordinateClaim 227 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_12, phase_linear_16_12, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_13 : integerCoordinateClaim 227 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_13, phase_linear_16_13, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_14 : integerCoordinateClaim 227 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_14, phase_linear_16_14, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_15 : integerCoordinateClaim 227 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_15, phase_linear_16_15, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_16 : integerCoordinateClaim 227 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_16, phase_linear_16_16, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_17 : integerCoordinateClaim 227 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_17, phase_linear_16_17, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_18 : integerCoordinateClaim 227 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_18, phase_linear_16_18, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_19 : integerCoordinateClaim 227 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_19, phase_linear_16_19, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_20 : integerCoordinateClaim 227 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_20, phase_linear_16_20, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_21 : integerCoordinateClaim 227 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_21, phase_linear_16_21, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_22 : integerCoordinateClaim 227 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_22, phase_linear_16_22, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

private theorem coordinate_227_23 : integerCoordinateClaim 227 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_227]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_227_0, scale_227_1, scale_227_2, phase_linear_6_23, phase_linear_16_23, gram_numerator_literal_57, gram_numerator_literal_95, gram_numerator_literal_102, denominator_literal_227, target_denominator_literal_227, target_numerator_literal_227]
  decide +kernel

theorem integer_residual_227 : integerResidualClaim 227 :=
  (Fin.cases coordinate_227_0 (Fin.cases coordinate_227_1 (Fin.cases coordinate_227_2 (Fin.cases coordinate_227_3 (Fin.cases coordinate_227_4 (Fin.cases coordinate_227_5 (Fin.cases coordinate_227_6 (Fin.cases coordinate_227_7 (Fin.cases coordinate_227_8 (Fin.cases coordinate_227_9 (Fin.cases coordinate_227_10 (Fin.cases coordinate_227_11 (Fin.cases coordinate_227_12 (Fin.cases coordinate_227_13 (Fin.cases coordinate_227_14 (Fin.cases coordinate_227_15 (Fin.cases coordinate_227_16 (Fin.cases coordinate_227_17 (Fin.cases coordinate_227_18 (Fin.cases coordinate_227_19 (Fin.cases coordinate_227_20 (Fin.cases coordinate_227_21 (Fin.cases coordinate_227_22 (Fin.cases coordinate_227_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
