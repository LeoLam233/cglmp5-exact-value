import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear04
import CGLMP5.SOSPhaseLinear14

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_11_0 : commonDenominator 11 / (gramDenominator 63 * phaseDenominator 14) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_11_1 : commonDenominator 11 / (gramDenominator 98 * phaseDenominator 4) = 1 := by
  decide +kernel

private theorem scale_11_2 : commonDenominator 11 / (gramDenominator 106 * phaseDenominator 4) = 1 := by
  decide +kernel

theorem denominator_divides_011 : ∀ f ∈ fiber 11, commonDenominator 11 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_11_0 : integerCoordinateClaim 11 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_0, phase_linear_14_0, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_1 : integerCoordinateClaim 11 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_1, phase_linear_14_1, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_2 : integerCoordinateClaim 11 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_2, phase_linear_14_2, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_3 : integerCoordinateClaim 11 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_3, phase_linear_14_3, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_4 : integerCoordinateClaim 11 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_4, phase_linear_14_4, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_5 : integerCoordinateClaim 11 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_5, phase_linear_14_5, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_6 : integerCoordinateClaim 11 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_6, phase_linear_14_6, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_7 : integerCoordinateClaim 11 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_7, phase_linear_14_7, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_8 : integerCoordinateClaim 11 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_8, phase_linear_14_8, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_9 : integerCoordinateClaim 11 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_9, phase_linear_14_9, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_10 : integerCoordinateClaim 11 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_10, phase_linear_14_10, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_11 : integerCoordinateClaim 11 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_11, phase_linear_14_11, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_12 : integerCoordinateClaim 11 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_12, phase_linear_14_12, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_13 : integerCoordinateClaim 11 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_13, phase_linear_14_13, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_14 : integerCoordinateClaim 11 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_14, phase_linear_14_14, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_15 : integerCoordinateClaim 11 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_15, phase_linear_14_15, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_16 : integerCoordinateClaim 11 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_16, phase_linear_14_16, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_17 : integerCoordinateClaim 11 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_17, phase_linear_14_17, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_18 : integerCoordinateClaim 11 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_18, phase_linear_14_18, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_19 : integerCoordinateClaim 11 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_19, phase_linear_14_19, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_20 : integerCoordinateClaim 11 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_20, phase_linear_14_20, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_21 : integerCoordinateClaim 11 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_21, phase_linear_14_21, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_22 : integerCoordinateClaim 11 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_22, phase_linear_14_22, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

private theorem coordinate_11_23 : integerCoordinateClaim 11 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_11_0, scale_11_1, scale_11_2, phase_linear_4_23, phase_linear_14_23, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_11, target_denominator_literal_11, target_numerator_literal_11]
  decide +kernel

theorem integer_residual_011 : integerResidualClaim 11 :=
  (Fin.cases coordinate_11_0 (Fin.cases coordinate_11_1 (Fin.cases coordinate_11_2 (Fin.cases coordinate_11_3 (Fin.cases coordinate_11_4 (Fin.cases coordinate_11_5 (Fin.cases coordinate_11_6 (Fin.cases coordinate_11_7 (Fin.cases coordinate_11_8 (Fin.cases coordinate_11_9 (Fin.cases coordinate_11_10 (Fin.cases coordinate_11_11 (Fin.cases coordinate_11_12 (Fin.cases coordinate_11_13 (Fin.cases coordinate_11_14 (Fin.cases coordinate_11_15 (Fin.cases coordinate_11_16 (Fin.cases coordinate_11_17 (Fin.cases coordinate_11_18 (Fin.cases coordinate_11_19 (Fin.cases coordinate_11_20 (Fin.cases coordinate_11_21 (Fin.cases coordinate_11_22 (Fin.cases coordinate_11_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
