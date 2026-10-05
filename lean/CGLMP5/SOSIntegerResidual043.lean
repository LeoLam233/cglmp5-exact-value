import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear01
import CGLMP5.SOSPhaseLinear06
import CGLMP5.SOSPhaseLinear09

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_43_0 : commonDenominator 43 / (gramDenominator 6 * phaseDenominator 1) = 501845005 := by
  decide +kernel

private theorem scale_43_1 : commonDenominator 43 / (gramDenominator 31 * phaseDenominator 6) = 978728409406056926918912099962962263888535306230093988 := by
  decide +kernel

private theorem scale_43_2 : commonDenominator 43 / (gramDenominator 42 * phaseDenominator 6) = 2 := by
  decide +kernel

private theorem scale_43_3 : commonDenominator 43 / (gramDenominator 118 * phaseDenominator 9) = 501845005 := by
  decide +kernel

theorem denominator_divides_043 : ∀ f ∈ fiber 43, commonDenominator 43 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_43_0 : integerCoordinateClaim 43 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_0, phase_linear_6_0, phase_linear_9_0, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_1 : integerCoordinateClaim 43 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_1, phase_linear_6_1, phase_linear_9_1, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_2 : integerCoordinateClaim 43 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_2, phase_linear_6_2, phase_linear_9_2, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_3 : integerCoordinateClaim 43 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_3, phase_linear_6_3, phase_linear_9_3, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_4 : integerCoordinateClaim 43 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_4, phase_linear_6_4, phase_linear_9_4, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_5 : integerCoordinateClaim 43 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_5, phase_linear_6_5, phase_linear_9_5, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_6 : integerCoordinateClaim 43 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_6, phase_linear_6_6, phase_linear_9_6, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_7 : integerCoordinateClaim 43 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_7, phase_linear_6_7, phase_linear_9_7, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_8 : integerCoordinateClaim 43 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_8, phase_linear_6_8, phase_linear_9_8, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_9 : integerCoordinateClaim 43 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_9, phase_linear_6_9, phase_linear_9_9, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_10 : integerCoordinateClaim 43 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_10, phase_linear_6_10, phase_linear_9_10, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_11 : integerCoordinateClaim 43 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_11, phase_linear_6_11, phase_linear_9_11, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_12 : integerCoordinateClaim 43 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_12, phase_linear_6_12, phase_linear_9_12, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_13 : integerCoordinateClaim 43 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_13, phase_linear_6_13, phase_linear_9_13, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_14 : integerCoordinateClaim 43 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_14, phase_linear_6_14, phase_linear_9_14, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_15 : integerCoordinateClaim 43 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_15, phase_linear_6_15, phase_linear_9_15, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_16 : integerCoordinateClaim 43 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_16, phase_linear_6_16, phase_linear_9_16, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_17 : integerCoordinateClaim 43 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_17, phase_linear_6_17, phase_linear_9_17, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_18 : integerCoordinateClaim 43 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_18, phase_linear_6_18, phase_linear_9_18, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_19 : integerCoordinateClaim 43 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_19, phase_linear_6_19, phase_linear_9_19, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_20 : integerCoordinateClaim 43 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_20, phase_linear_6_20, phase_linear_9_20, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_21 : integerCoordinateClaim 43 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_21, phase_linear_6_21, phase_linear_9_21, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_22 : integerCoordinateClaim 43 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_22, phase_linear_6_22, phase_linear_9_22, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

private theorem coordinate_43_23 : integerCoordinateClaim 43 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_43]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_43_0, scale_43_1, scale_43_2, scale_43_3, phase_linear_1_23, phase_linear_6_23, phase_linear_9_23, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_43, target_denominator_literal_43, target_numerator_literal_43]
  decide +kernel

theorem integer_residual_043 : integerResidualClaim 43 :=
  (Fin.cases coordinate_43_0 (Fin.cases coordinate_43_1 (Fin.cases coordinate_43_2 (Fin.cases coordinate_43_3 (Fin.cases coordinate_43_4 (Fin.cases coordinate_43_5 (Fin.cases coordinate_43_6 (Fin.cases coordinate_43_7 (Fin.cases coordinate_43_8 (Fin.cases coordinate_43_9 (Fin.cases coordinate_43_10 (Fin.cases coordinate_43_11 (Fin.cases coordinate_43_12 (Fin.cases coordinate_43_13 (Fin.cases coordinate_43_14 (Fin.cases coordinate_43_15 (Fin.cases coordinate_43_16 (Fin.cases coordinate_43_17 (Fin.cases coordinate_43_18 (Fin.cases coordinate_43_19 (Fin.cases coordinate_43_20 (Fin.cases coordinate_43_21 (Fin.cases coordinate_43_22 (Fin.cases coordinate_43_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
