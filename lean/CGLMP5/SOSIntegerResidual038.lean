import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear06
import CGLMP5.SOSPhaseLinear16

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_38_0 : commonDenominator 38 / (gramDenominator 63 * phaseDenominator 6) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_38_1 : commonDenominator 38 / (gramDenominator 98 * phaseDenominator 16) = 1 := by
  decide +kernel

private theorem scale_38_2 : commonDenominator 38 / (gramDenominator 106 * phaseDenominator 16) = 1 := by
  decide +kernel

theorem denominator_divides_038 : ∀ f ∈ fiber 38, commonDenominator 38 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_38_0 : integerCoordinateClaim 38 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_0, phase_linear_16_0, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_1 : integerCoordinateClaim 38 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_1, phase_linear_16_1, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_2 : integerCoordinateClaim 38 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_2, phase_linear_16_2, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_3 : integerCoordinateClaim 38 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_3, phase_linear_16_3, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_4 : integerCoordinateClaim 38 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_4, phase_linear_16_4, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_5 : integerCoordinateClaim 38 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_5, phase_linear_16_5, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_6 : integerCoordinateClaim 38 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_6, phase_linear_16_6, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_7 : integerCoordinateClaim 38 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_7, phase_linear_16_7, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_8 : integerCoordinateClaim 38 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_8, phase_linear_16_8, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_9 : integerCoordinateClaim 38 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_9, phase_linear_16_9, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_10 : integerCoordinateClaim 38 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_10, phase_linear_16_10, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_11 : integerCoordinateClaim 38 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_11, phase_linear_16_11, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_12 : integerCoordinateClaim 38 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_12, phase_linear_16_12, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_13 : integerCoordinateClaim 38 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_13, phase_linear_16_13, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_14 : integerCoordinateClaim 38 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_14, phase_linear_16_14, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_15 : integerCoordinateClaim 38 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_15, phase_linear_16_15, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_16 : integerCoordinateClaim 38 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_16, phase_linear_16_16, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_17 : integerCoordinateClaim 38 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_17, phase_linear_16_17, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_18 : integerCoordinateClaim 38 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_18, phase_linear_16_18, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_19 : integerCoordinateClaim 38 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_19, phase_linear_16_19, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_20 : integerCoordinateClaim 38 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_20, phase_linear_16_20, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_21 : integerCoordinateClaim 38 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_21, phase_linear_16_21, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_22 : integerCoordinateClaim 38 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_22, phase_linear_16_22, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

private theorem coordinate_38_23 : integerCoordinateClaim 38 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_38]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_38_0, scale_38_1, scale_38_2, phase_linear_6_23, phase_linear_16_23, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_38, target_denominator_literal_38, target_numerator_literal_38]
  decide +kernel

theorem integer_residual_038 : integerResidualClaim 38 :=
  (Fin.cases coordinate_38_0 (Fin.cases coordinate_38_1 (Fin.cases coordinate_38_2 (Fin.cases coordinate_38_3 (Fin.cases coordinate_38_4 (Fin.cases coordinate_38_5 (Fin.cases coordinate_38_6 (Fin.cases coordinate_38_7 (Fin.cases coordinate_38_8 (Fin.cases coordinate_38_9 (Fin.cases coordinate_38_10 (Fin.cases coordinate_38_11 (Fin.cases coordinate_38_12 (Fin.cases coordinate_38_13 (Fin.cases coordinate_38_14 (Fin.cases coordinate_38_15 (Fin.cases coordinate_38_16 (Fin.cases coordinate_38_17 (Fin.cases coordinate_38_18 (Fin.cases coordinate_38_19 (Fin.cases coordinate_38_20 (Fin.cases coordinate_38_21 (Fin.cases coordinate_38_22 (Fin.cases coordinate_38_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
