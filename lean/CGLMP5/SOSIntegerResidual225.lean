import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear02
import CGLMP5.SOSPhaseLinear05
import CGLMP5.SOSPhaseLinear17

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_225_0 : commonDenominator 225 / (gramDenominator 6 * phaseDenominator 17) = 501845005 := by
  decide +kernel

private theorem scale_225_1 : commonDenominator 225 / (gramDenominator 31 * phaseDenominator 2) = 978728409406056926918912099962962263888535306230093988 := by
  decide +kernel

private theorem scale_225_2 : commonDenominator 225 / (gramDenominator 42 * phaseDenominator 2) = 2 := by
  decide +kernel

private theorem scale_225_3 : commonDenominator 225 / (gramDenominator 118 * phaseDenominator 5) = 4014760040 := by
  decide +kernel

theorem denominator_divides_225 : ∀ f ∈ fiber 225, commonDenominator 225 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_225_0 : integerCoordinateClaim 225 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_0, phase_linear_5_0, phase_linear_17_0, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_1 : integerCoordinateClaim 225 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_1, phase_linear_5_1, phase_linear_17_1, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_2 : integerCoordinateClaim 225 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_2, phase_linear_5_2, phase_linear_17_2, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_3 : integerCoordinateClaim 225 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_3, phase_linear_5_3, phase_linear_17_3, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_4 : integerCoordinateClaim 225 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_4, phase_linear_5_4, phase_linear_17_4, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_5 : integerCoordinateClaim 225 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_5, phase_linear_5_5, phase_linear_17_5, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_6 : integerCoordinateClaim 225 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_6, phase_linear_5_6, phase_linear_17_6, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_7 : integerCoordinateClaim 225 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_7, phase_linear_5_7, phase_linear_17_7, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_8 : integerCoordinateClaim 225 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_8, phase_linear_5_8, phase_linear_17_8, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_9 : integerCoordinateClaim 225 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_9, phase_linear_5_9, phase_linear_17_9, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_10 : integerCoordinateClaim 225 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_10, phase_linear_5_10, phase_linear_17_10, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_11 : integerCoordinateClaim 225 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_11, phase_linear_5_11, phase_linear_17_11, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_12 : integerCoordinateClaim 225 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_12, phase_linear_5_12, phase_linear_17_12, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_13 : integerCoordinateClaim 225 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_13, phase_linear_5_13, phase_linear_17_13, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_14 : integerCoordinateClaim 225 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_14, phase_linear_5_14, phase_linear_17_14, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_15 : integerCoordinateClaim 225 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_15, phase_linear_5_15, phase_linear_17_15, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_16 : integerCoordinateClaim 225 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_16, phase_linear_5_16, phase_linear_17_16, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_17 : integerCoordinateClaim 225 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_17, phase_linear_5_17, phase_linear_17_17, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_18 : integerCoordinateClaim 225 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_18, phase_linear_5_18, phase_linear_17_18, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_19 : integerCoordinateClaim 225 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_19, phase_linear_5_19, phase_linear_17_19, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_20 : integerCoordinateClaim 225 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_20, phase_linear_5_20, phase_linear_17_20, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_21 : integerCoordinateClaim 225 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_21, phase_linear_5_21, phase_linear_17_21, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_22 : integerCoordinateClaim 225 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_22, phase_linear_5_22, phase_linear_17_22, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

private theorem coordinate_225_23 : integerCoordinateClaim 225 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_225]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_225_0, scale_225_1, scale_225_2, scale_225_3, phase_linear_2_23, phase_linear_5_23, phase_linear_17_23, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_225, target_denominator_literal_225, target_numerator_literal_225]
  decide +kernel

theorem integer_residual_225 : integerResidualClaim 225 :=
  (Fin.cases coordinate_225_0 (Fin.cases coordinate_225_1 (Fin.cases coordinate_225_2 (Fin.cases coordinate_225_3 (Fin.cases coordinate_225_4 (Fin.cases coordinate_225_5 (Fin.cases coordinate_225_6 (Fin.cases coordinate_225_7 (Fin.cases coordinate_225_8 (Fin.cases coordinate_225_9 (Fin.cases coordinate_225_10 (Fin.cases coordinate_225_11 (Fin.cases coordinate_225_12 (Fin.cases coordinate_225_13 (Fin.cases coordinate_225_14 (Fin.cases coordinate_225_15 (Fin.cases coordinate_225_16 (Fin.cases coordinate_225_17 (Fin.cases coordinate_225_18 (Fin.cases coordinate_225_19 (Fin.cases coordinate_225_20 (Fin.cases coordinate_225_21 (Fin.cases coordinate_225_22 (Fin.cases coordinate_225_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
