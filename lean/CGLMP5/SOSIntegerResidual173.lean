import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear04
import CGLMP5.SOSPhaseLinear14

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_173_0 : commonDenominator 173 / (gramDenominator 63 * phaseDenominator 14) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_173_1 : commonDenominator 173 / (gramDenominator 98 * phaseDenominator 4) = 1 := by
  decide +kernel

private theorem scale_173_2 : commonDenominator 173 / (gramDenominator 106 * phaseDenominator 4) = 1 := by
  decide +kernel

theorem denominator_divides_173 : ∀ f ∈ fiber 173, commonDenominator 173 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_173_0 : integerCoordinateClaim 173 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_0, phase_linear_14_0, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_1 : integerCoordinateClaim 173 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_1, phase_linear_14_1, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_2 : integerCoordinateClaim 173 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_2, phase_linear_14_2, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_3 : integerCoordinateClaim 173 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_3, phase_linear_14_3, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_4 : integerCoordinateClaim 173 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_4, phase_linear_14_4, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_5 : integerCoordinateClaim 173 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_5, phase_linear_14_5, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_6 : integerCoordinateClaim 173 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_6, phase_linear_14_6, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_7 : integerCoordinateClaim 173 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_7, phase_linear_14_7, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_8 : integerCoordinateClaim 173 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_8, phase_linear_14_8, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_9 : integerCoordinateClaim 173 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_9, phase_linear_14_9, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_10 : integerCoordinateClaim 173 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_10, phase_linear_14_10, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_11 : integerCoordinateClaim 173 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_11, phase_linear_14_11, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_12 : integerCoordinateClaim 173 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_12, phase_linear_14_12, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_13 : integerCoordinateClaim 173 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_13, phase_linear_14_13, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_14 : integerCoordinateClaim 173 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_14, phase_linear_14_14, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_15 : integerCoordinateClaim 173 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_15, phase_linear_14_15, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_16 : integerCoordinateClaim 173 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_16, phase_linear_14_16, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_17 : integerCoordinateClaim 173 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_17, phase_linear_14_17, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_18 : integerCoordinateClaim 173 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_18, phase_linear_14_18, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_19 : integerCoordinateClaim 173 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_19, phase_linear_14_19, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_20 : integerCoordinateClaim 173 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_20, phase_linear_14_20, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_21 : integerCoordinateClaim 173 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_21, phase_linear_14_21, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_22 : integerCoordinateClaim 173 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_22, phase_linear_14_22, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

private theorem coordinate_173_23 : integerCoordinateClaim 173 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_173]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_173_0, scale_173_1, scale_173_2, phase_linear_4_23, phase_linear_14_23, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_173, target_denominator_literal_173, target_numerator_literal_173]
  decide +kernel

theorem integer_residual_173 : integerResidualClaim 173 :=
  (Fin.cases coordinate_173_0 (Fin.cases coordinate_173_1 (Fin.cases coordinate_173_2 (Fin.cases coordinate_173_3 (Fin.cases coordinate_173_4 (Fin.cases coordinate_173_5 (Fin.cases coordinate_173_6 (Fin.cases coordinate_173_7 (Fin.cases coordinate_173_8 (Fin.cases coordinate_173_9 (Fin.cases coordinate_173_10 (Fin.cases coordinate_173_11 (Fin.cases coordinate_173_12 (Fin.cases coordinate_173_13 (Fin.cases coordinate_173_14 (Fin.cases coordinate_173_15 (Fin.cases coordinate_173_16 (Fin.cases coordinate_173_17 (Fin.cases coordinate_173_18 (Fin.cases coordinate_173_19 (Fin.cases coordinate_173_20 (Fin.cases coordinate_173_21 (Fin.cases coordinate_173_22 (Fin.cases coordinate_173_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
