import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear06
import CGLMP5.SOSPhaseLinear16

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_146_0 : commonDenominator 146 / (gramDenominator 63 * phaseDenominator 6) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_146_1 : commonDenominator 146 / (gramDenominator 98 * phaseDenominator 16) = 1 := by
  decide +kernel

private theorem scale_146_2 : commonDenominator 146 / (gramDenominator 106 * phaseDenominator 16) = 1 := by
  decide +kernel

theorem denominator_divides_146 : ∀ f ∈ fiber 146, commonDenominator 146 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_146_0 : integerCoordinateClaim 146 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_0, phase_linear_16_0, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_1 : integerCoordinateClaim 146 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_1, phase_linear_16_1, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_2 : integerCoordinateClaim 146 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_2, phase_linear_16_2, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_3 : integerCoordinateClaim 146 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_3, phase_linear_16_3, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_4 : integerCoordinateClaim 146 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_4, phase_linear_16_4, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_5 : integerCoordinateClaim 146 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_5, phase_linear_16_5, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_6 : integerCoordinateClaim 146 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_6, phase_linear_16_6, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_7 : integerCoordinateClaim 146 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_7, phase_linear_16_7, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_8 : integerCoordinateClaim 146 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_8, phase_linear_16_8, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_9 : integerCoordinateClaim 146 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_9, phase_linear_16_9, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_10 : integerCoordinateClaim 146 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_10, phase_linear_16_10, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_11 : integerCoordinateClaim 146 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_11, phase_linear_16_11, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_12 : integerCoordinateClaim 146 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_12, phase_linear_16_12, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_13 : integerCoordinateClaim 146 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_13, phase_linear_16_13, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_14 : integerCoordinateClaim 146 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_14, phase_linear_16_14, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_15 : integerCoordinateClaim 146 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_15, phase_linear_16_15, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_16 : integerCoordinateClaim 146 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_16, phase_linear_16_16, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_17 : integerCoordinateClaim 146 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_17, phase_linear_16_17, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_18 : integerCoordinateClaim 146 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_18, phase_linear_16_18, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_19 : integerCoordinateClaim 146 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_19, phase_linear_16_19, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_20 : integerCoordinateClaim 146 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_20, phase_linear_16_20, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_21 : integerCoordinateClaim 146 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_21, phase_linear_16_21, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_22 : integerCoordinateClaim 146 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_22, phase_linear_16_22, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

private theorem coordinate_146_23 : integerCoordinateClaim 146 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_146]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_146_0, scale_146_1, scale_146_2, phase_linear_6_23, phase_linear_16_23, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_146, target_denominator_literal_146, target_numerator_literal_146]
  decide +kernel

theorem integer_residual_146 : integerResidualClaim 146 :=
  (Fin.cases coordinate_146_0 (Fin.cases coordinate_146_1 (Fin.cases coordinate_146_2 (Fin.cases coordinate_146_3 (Fin.cases coordinate_146_4 (Fin.cases coordinate_146_5 (Fin.cases coordinate_146_6 (Fin.cases coordinate_146_7 (Fin.cases coordinate_146_8 (Fin.cases coordinate_146_9 (Fin.cases coordinate_146_10 (Fin.cases coordinate_146_11 (Fin.cases coordinate_146_12 (Fin.cases coordinate_146_13 (Fin.cases coordinate_146_14 (Fin.cases coordinate_146_15 (Fin.cases coordinate_146_16 (Fin.cases coordinate_146_17 (Fin.cases coordinate_146_18 (Fin.cases coordinate_146_19 (Fin.cases coordinate_146_20 (Fin.cases coordinate_146_21 (Fin.cases coordinate_146_22 (Fin.cases coordinate_146_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
