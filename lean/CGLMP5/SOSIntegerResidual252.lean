import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear01
import CGLMP5.SOSPhaseLinear13
import CGLMP5.SOSPhaseLinear18

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_252_0 : commonDenominator 252 / (gramDenominator 6 * phaseDenominator 13) = 501845005 := by
  decide +kernel

private theorem scale_252_1 : commonDenominator 252 / (gramDenominator 31 * phaseDenominator 18) = 978728409406056926918912099962962263888535306230093988 := by
  decide +kernel

private theorem scale_252_2 : commonDenominator 252 / (gramDenominator 42 * phaseDenominator 18) = 2 := by
  decide +kernel

private theorem scale_252_3 : commonDenominator 252 / (gramDenominator 118 * phaseDenominator 1) = 1003690010 := by
  decide +kernel

theorem denominator_divides_252 : ∀ f ∈ fiber 252, commonDenominator 252 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_252_0 : integerCoordinateClaim 252 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_0, phase_linear_13_0, phase_linear_18_0, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_1 : integerCoordinateClaim 252 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_1, phase_linear_13_1, phase_linear_18_1, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_2 : integerCoordinateClaim 252 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_2, phase_linear_13_2, phase_linear_18_2, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_3 : integerCoordinateClaim 252 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_3, phase_linear_13_3, phase_linear_18_3, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_4 : integerCoordinateClaim 252 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_4, phase_linear_13_4, phase_linear_18_4, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_5 : integerCoordinateClaim 252 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_5, phase_linear_13_5, phase_linear_18_5, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_6 : integerCoordinateClaim 252 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_6, phase_linear_13_6, phase_linear_18_6, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_7 : integerCoordinateClaim 252 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_7, phase_linear_13_7, phase_linear_18_7, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_8 : integerCoordinateClaim 252 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_8, phase_linear_13_8, phase_linear_18_8, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_9 : integerCoordinateClaim 252 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_9, phase_linear_13_9, phase_linear_18_9, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_10 : integerCoordinateClaim 252 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_10, phase_linear_13_10, phase_linear_18_10, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_11 : integerCoordinateClaim 252 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_11, phase_linear_13_11, phase_linear_18_11, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_12 : integerCoordinateClaim 252 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_12, phase_linear_13_12, phase_linear_18_12, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_13 : integerCoordinateClaim 252 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_13, phase_linear_13_13, phase_linear_18_13, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_14 : integerCoordinateClaim 252 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_14, phase_linear_13_14, phase_linear_18_14, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_15 : integerCoordinateClaim 252 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_15, phase_linear_13_15, phase_linear_18_15, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_16 : integerCoordinateClaim 252 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_16, phase_linear_13_16, phase_linear_18_16, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_17 : integerCoordinateClaim 252 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_17, phase_linear_13_17, phase_linear_18_17, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_18 : integerCoordinateClaim 252 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_18, phase_linear_13_18, phase_linear_18_18, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_19 : integerCoordinateClaim 252 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_19, phase_linear_13_19, phase_linear_18_19, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_20 : integerCoordinateClaim 252 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_20, phase_linear_13_20, phase_linear_18_20, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_21 : integerCoordinateClaim 252 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_21, phase_linear_13_21, phase_linear_18_21, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_22 : integerCoordinateClaim 252 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_22, phase_linear_13_22, phase_linear_18_22, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

private theorem coordinate_252_23 : integerCoordinateClaim 252 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_252]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_252_0, scale_252_1, scale_252_2, scale_252_3, phase_linear_1_23, phase_linear_13_23, phase_linear_18_23, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_252, target_denominator_literal_252, target_numerator_literal_252]
  decide +kernel

theorem integer_residual_252 : integerResidualClaim 252 :=
  (Fin.cases coordinate_252_0 (Fin.cases coordinate_252_1 (Fin.cases coordinate_252_2 (Fin.cases coordinate_252_3 (Fin.cases coordinate_252_4 (Fin.cases coordinate_252_5 (Fin.cases coordinate_252_6 (Fin.cases coordinate_252_7 (Fin.cases coordinate_252_8 (Fin.cases coordinate_252_9 (Fin.cases coordinate_252_10 (Fin.cases coordinate_252_11 (Fin.cases coordinate_252_12 (Fin.cases coordinate_252_13 (Fin.cases coordinate_252_14 (Fin.cases coordinate_252_15 (Fin.cases coordinate_252_16 (Fin.cases coordinate_252_17 (Fin.cases coordinate_252_18 (Fin.cases coordinate_252_19 (Fin.cases coordinate_252_20 (Fin.cases coordinate_252_21 (Fin.cases coordinate_252_22 (Fin.cases coordinate_252_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
