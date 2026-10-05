import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear01
import CGLMP5.SOSPhaseLinear06
import CGLMP5.SOSPhaseLinear09

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_145_0 : commonDenominator 145 / (gramDenominator 6 * phaseDenominator 1) = 501845005 := by
  decide +kernel

private theorem scale_145_1 : commonDenominator 145 / (gramDenominator 31 * phaseDenominator 6) = 978728409406056926918912099962962263888535306230093988 := by
  decide +kernel

private theorem scale_145_2 : commonDenominator 145 / (gramDenominator 42 * phaseDenominator 6) = 2 := by
  decide +kernel

private theorem scale_145_3 : commonDenominator 145 / (gramDenominator 118 * phaseDenominator 9) = 501845005 := by
  decide +kernel

theorem denominator_divides_145 : ∀ f ∈ fiber 145, commonDenominator 145 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_145_0 : integerCoordinateClaim 145 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_0, phase_linear_6_0, phase_linear_9_0, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_1 : integerCoordinateClaim 145 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_1, phase_linear_6_1, phase_linear_9_1, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_2 : integerCoordinateClaim 145 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_2, phase_linear_6_2, phase_linear_9_2, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_3 : integerCoordinateClaim 145 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_3, phase_linear_6_3, phase_linear_9_3, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_4 : integerCoordinateClaim 145 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_4, phase_linear_6_4, phase_linear_9_4, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_5 : integerCoordinateClaim 145 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_5, phase_linear_6_5, phase_linear_9_5, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_6 : integerCoordinateClaim 145 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_6, phase_linear_6_6, phase_linear_9_6, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_7 : integerCoordinateClaim 145 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_7, phase_linear_6_7, phase_linear_9_7, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_8 : integerCoordinateClaim 145 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_8, phase_linear_6_8, phase_linear_9_8, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_9 : integerCoordinateClaim 145 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_9, phase_linear_6_9, phase_linear_9_9, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_10 : integerCoordinateClaim 145 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_10, phase_linear_6_10, phase_linear_9_10, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_11 : integerCoordinateClaim 145 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_11, phase_linear_6_11, phase_linear_9_11, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_12 : integerCoordinateClaim 145 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_12, phase_linear_6_12, phase_linear_9_12, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_13 : integerCoordinateClaim 145 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_13, phase_linear_6_13, phase_linear_9_13, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_14 : integerCoordinateClaim 145 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_14, phase_linear_6_14, phase_linear_9_14, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_15 : integerCoordinateClaim 145 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_15, phase_linear_6_15, phase_linear_9_15, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_16 : integerCoordinateClaim 145 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_16, phase_linear_6_16, phase_linear_9_16, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_17 : integerCoordinateClaim 145 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_17, phase_linear_6_17, phase_linear_9_17, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_18 : integerCoordinateClaim 145 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_18, phase_linear_6_18, phase_linear_9_18, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_19 : integerCoordinateClaim 145 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_19, phase_linear_6_19, phase_linear_9_19, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_20 : integerCoordinateClaim 145 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_20, phase_linear_6_20, phase_linear_9_20, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_21 : integerCoordinateClaim 145 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_21, phase_linear_6_21, phase_linear_9_21, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_22 : integerCoordinateClaim 145 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_22, phase_linear_6_22, phase_linear_9_22, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

private theorem coordinate_145_23 : integerCoordinateClaim 145 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_145]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_145_0, scale_145_1, scale_145_2, scale_145_3, phase_linear_1_23, phase_linear_6_23, phase_linear_9_23, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_145, target_denominator_literal_145, target_numerator_literal_145]
  decide +kernel

theorem integer_residual_145 : integerResidualClaim 145 :=
  (Fin.cases coordinate_145_0 (Fin.cases coordinate_145_1 (Fin.cases coordinate_145_2 (Fin.cases coordinate_145_3 (Fin.cases coordinate_145_4 (Fin.cases coordinate_145_5 (Fin.cases coordinate_145_6 (Fin.cases coordinate_145_7 (Fin.cases coordinate_145_8 (Fin.cases coordinate_145_9 (Fin.cases coordinate_145_10 (Fin.cases coordinate_145_11 (Fin.cases coordinate_145_12 (Fin.cases coordinate_145_13 (Fin.cases coordinate_145_14 (Fin.cases coordinate_145_15 (Fin.cases coordinate_145_16 (Fin.cases coordinate_145_17 (Fin.cases coordinate_145_18 (Fin.cases coordinate_145_19 (Fin.cases coordinate_145_20 (Fin.cases coordinate_145_21 (Fin.cases coordinate_145_22 (Fin.cases coordinate_145_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
