import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear02
import CGLMP5.SOSPhaseLinear05
import CGLMP5.SOSPhaseLinear17

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_117_0 : commonDenominator 117 / (gramDenominator 6 * phaseDenominator 17) = 501845005 := by
  decide +kernel

private theorem scale_117_1 : commonDenominator 117 / (gramDenominator 31 * phaseDenominator 2) = 978728409406056926918912099962962263888535306230093988 := by
  decide +kernel

private theorem scale_117_2 : commonDenominator 117 / (gramDenominator 42 * phaseDenominator 2) = 2 := by
  decide +kernel

private theorem scale_117_3 : commonDenominator 117 / (gramDenominator 118 * phaseDenominator 5) = 4014760040 := by
  decide +kernel

theorem denominator_divides_117 : ∀ f ∈ fiber 117, commonDenominator 117 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_117_0 : integerCoordinateClaim 117 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_0, phase_linear_5_0, phase_linear_17_0, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_1 : integerCoordinateClaim 117 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_1, phase_linear_5_1, phase_linear_17_1, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_2 : integerCoordinateClaim 117 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_2, phase_linear_5_2, phase_linear_17_2, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_3 : integerCoordinateClaim 117 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_3, phase_linear_5_3, phase_linear_17_3, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_4 : integerCoordinateClaim 117 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_4, phase_linear_5_4, phase_linear_17_4, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_5 : integerCoordinateClaim 117 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_5, phase_linear_5_5, phase_linear_17_5, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_6 : integerCoordinateClaim 117 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_6, phase_linear_5_6, phase_linear_17_6, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_7 : integerCoordinateClaim 117 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_7, phase_linear_5_7, phase_linear_17_7, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_8 : integerCoordinateClaim 117 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_8, phase_linear_5_8, phase_linear_17_8, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_9 : integerCoordinateClaim 117 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_9, phase_linear_5_9, phase_linear_17_9, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_10 : integerCoordinateClaim 117 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_10, phase_linear_5_10, phase_linear_17_10, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_11 : integerCoordinateClaim 117 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_11, phase_linear_5_11, phase_linear_17_11, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_12 : integerCoordinateClaim 117 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_12, phase_linear_5_12, phase_linear_17_12, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_13 : integerCoordinateClaim 117 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_13, phase_linear_5_13, phase_linear_17_13, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_14 : integerCoordinateClaim 117 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_14, phase_linear_5_14, phase_linear_17_14, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_15 : integerCoordinateClaim 117 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_15, phase_linear_5_15, phase_linear_17_15, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_16 : integerCoordinateClaim 117 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_16, phase_linear_5_16, phase_linear_17_16, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_17 : integerCoordinateClaim 117 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_17, phase_linear_5_17, phase_linear_17_17, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_18 : integerCoordinateClaim 117 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_18, phase_linear_5_18, phase_linear_17_18, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_19 : integerCoordinateClaim 117 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_19, phase_linear_5_19, phase_linear_17_19, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_20 : integerCoordinateClaim 117 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_20, phase_linear_5_20, phase_linear_17_20, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_21 : integerCoordinateClaim 117 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_21, phase_linear_5_21, phase_linear_17_21, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_22 : integerCoordinateClaim 117 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_22, phase_linear_5_22, phase_linear_17_22, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

private theorem coordinate_117_23 : integerCoordinateClaim 117 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_117]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_117_0, scale_117_1, scale_117_2, scale_117_3, phase_linear_2_23, phase_linear_5_23, phase_linear_17_23, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_117, target_denominator_literal_117, target_numerator_literal_117]
  decide +kernel

theorem integer_residual_117 : integerResidualClaim 117 :=
  (Fin.cases coordinate_117_0 (Fin.cases coordinate_117_1 (Fin.cases coordinate_117_2 (Fin.cases coordinate_117_3 (Fin.cases coordinate_117_4 (Fin.cases coordinate_117_5 (Fin.cases coordinate_117_6 (Fin.cases coordinate_117_7 (Fin.cases coordinate_117_8 (Fin.cases coordinate_117_9 (Fin.cases coordinate_117_10 (Fin.cases coordinate_117_11 (Fin.cases coordinate_117_12 (Fin.cases coordinate_117_13 (Fin.cases coordinate_117_14 (Fin.cases coordinate_117_15 (Fin.cases coordinate_117_16 (Fin.cases coordinate_117_17 (Fin.cases coordinate_117_18 (Fin.cases coordinate_117_19 (Fin.cases coordinate_117_20 (Fin.cases coordinate_117_21 (Fin.cases coordinate_117_22 (Fin.cases coordinate_117_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
