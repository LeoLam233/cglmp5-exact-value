import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear01
import CGLMP5.SOSPhaseLinear13
import CGLMP5.SOSPhaseLinear18

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_90_0 : commonDenominator 90 / (gramDenominator 6 * phaseDenominator 13) = 501845005 := by
  decide +kernel

private theorem scale_90_1 : commonDenominator 90 / (gramDenominator 31 * phaseDenominator 18) = 978728409406056926918912099962962263888535306230093988 := by
  decide +kernel

private theorem scale_90_2 : commonDenominator 90 / (gramDenominator 42 * phaseDenominator 18) = 2 := by
  decide +kernel

private theorem scale_90_3 : commonDenominator 90 / (gramDenominator 118 * phaseDenominator 1) = 1003690010 := by
  decide +kernel

theorem denominator_divides_090 : ∀ f ∈ fiber 90, commonDenominator 90 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_90_0 : integerCoordinateClaim 90 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_0, phase_linear_13_0, phase_linear_18_0, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_1 : integerCoordinateClaim 90 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_1, phase_linear_13_1, phase_linear_18_1, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_2 : integerCoordinateClaim 90 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_2, phase_linear_13_2, phase_linear_18_2, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_3 : integerCoordinateClaim 90 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_3, phase_linear_13_3, phase_linear_18_3, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_4 : integerCoordinateClaim 90 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_4, phase_linear_13_4, phase_linear_18_4, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_5 : integerCoordinateClaim 90 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_5, phase_linear_13_5, phase_linear_18_5, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_6 : integerCoordinateClaim 90 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_6, phase_linear_13_6, phase_linear_18_6, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_7 : integerCoordinateClaim 90 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_7, phase_linear_13_7, phase_linear_18_7, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_8 : integerCoordinateClaim 90 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_8, phase_linear_13_8, phase_linear_18_8, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_9 : integerCoordinateClaim 90 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_9, phase_linear_13_9, phase_linear_18_9, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_10 : integerCoordinateClaim 90 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_10, phase_linear_13_10, phase_linear_18_10, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_11 : integerCoordinateClaim 90 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_11, phase_linear_13_11, phase_linear_18_11, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_12 : integerCoordinateClaim 90 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_12, phase_linear_13_12, phase_linear_18_12, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_13 : integerCoordinateClaim 90 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_13, phase_linear_13_13, phase_linear_18_13, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_14 : integerCoordinateClaim 90 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_14, phase_linear_13_14, phase_linear_18_14, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_15 : integerCoordinateClaim 90 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_15, phase_linear_13_15, phase_linear_18_15, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_16 : integerCoordinateClaim 90 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_16, phase_linear_13_16, phase_linear_18_16, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_17 : integerCoordinateClaim 90 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_17, phase_linear_13_17, phase_linear_18_17, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_18 : integerCoordinateClaim 90 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_18, phase_linear_13_18, phase_linear_18_18, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_19 : integerCoordinateClaim 90 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_19, phase_linear_13_19, phase_linear_18_19, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_20 : integerCoordinateClaim 90 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_20, phase_linear_13_20, phase_linear_18_20, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_21 : integerCoordinateClaim 90 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_21, phase_linear_13_21, phase_linear_18_21, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_22 : integerCoordinateClaim 90 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_22, phase_linear_13_22, phase_linear_18_22, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

private theorem coordinate_90_23 : integerCoordinateClaim 90 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_90]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_90_0, scale_90_1, scale_90_2, scale_90_3, phase_linear_1_23, phase_linear_13_23, phase_linear_18_23, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_90, target_denominator_literal_90, target_numerator_literal_90]
  decide +kernel

theorem integer_residual_090 : integerResidualClaim 90 :=
  (Fin.cases coordinate_90_0 (Fin.cases coordinate_90_1 (Fin.cases coordinate_90_2 (Fin.cases coordinate_90_3 (Fin.cases coordinate_90_4 (Fin.cases coordinate_90_5 (Fin.cases coordinate_90_6 (Fin.cases coordinate_90_7 (Fin.cases coordinate_90_8 (Fin.cases coordinate_90_9 (Fin.cases coordinate_90_10 (Fin.cases coordinate_90_11 (Fin.cases coordinate_90_12 (Fin.cases coordinate_90_13 (Fin.cases coordinate_90_14 (Fin.cases coordinate_90_15 (Fin.cases coordinate_90_16 (Fin.cases coordinate_90_17 (Fin.cases coordinate_90_18 (Fin.cases coordinate_90_19 (Fin.cases coordinate_90_20 (Fin.cases coordinate_90_21 (Fin.cases coordinate_90_22 (Fin.cases coordinate_90_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
