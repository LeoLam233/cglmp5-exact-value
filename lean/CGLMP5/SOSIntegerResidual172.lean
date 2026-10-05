import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear01
import CGLMP5.SOSPhaseLinear06
import CGLMP5.SOSPhaseLinear09

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_172_0 : commonDenominator 172 / (gramDenominator 6 * phaseDenominator 1) = 501845005 := by
  decide +kernel

private theorem scale_172_1 : commonDenominator 172 / (gramDenominator 31 * phaseDenominator 6) = 978728409406056926918912099962962263888535306230093988 := by
  decide +kernel

private theorem scale_172_2 : commonDenominator 172 / (gramDenominator 42 * phaseDenominator 6) = 2 := by
  decide +kernel

private theorem scale_172_3 : commonDenominator 172 / (gramDenominator 118 * phaseDenominator 9) = 501845005 := by
  decide +kernel

theorem denominator_divides_172 : ∀ f ∈ fiber 172, commonDenominator 172 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_172_0 : integerCoordinateClaim 172 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_0, phase_linear_6_0, phase_linear_9_0, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_1 : integerCoordinateClaim 172 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_1, phase_linear_6_1, phase_linear_9_1, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_2 : integerCoordinateClaim 172 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_2, phase_linear_6_2, phase_linear_9_2, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_3 : integerCoordinateClaim 172 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_3, phase_linear_6_3, phase_linear_9_3, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_4 : integerCoordinateClaim 172 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_4, phase_linear_6_4, phase_linear_9_4, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_5 : integerCoordinateClaim 172 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_5, phase_linear_6_5, phase_linear_9_5, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_6 : integerCoordinateClaim 172 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_6, phase_linear_6_6, phase_linear_9_6, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_7 : integerCoordinateClaim 172 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_7, phase_linear_6_7, phase_linear_9_7, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_8 : integerCoordinateClaim 172 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_8, phase_linear_6_8, phase_linear_9_8, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_9 : integerCoordinateClaim 172 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_9, phase_linear_6_9, phase_linear_9_9, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_10 : integerCoordinateClaim 172 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_10, phase_linear_6_10, phase_linear_9_10, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_11 : integerCoordinateClaim 172 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_11, phase_linear_6_11, phase_linear_9_11, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_12 : integerCoordinateClaim 172 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_12, phase_linear_6_12, phase_linear_9_12, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_13 : integerCoordinateClaim 172 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_13, phase_linear_6_13, phase_linear_9_13, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_14 : integerCoordinateClaim 172 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_14, phase_linear_6_14, phase_linear_9_14, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_15 : integerCoordinateClaim 172 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_15, phase_linear_6_15, phase_linear_9_15, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_16 : integerCoordinateClaim 172 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_16, phase_linear_6_16, phase_linear_9_16, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_17 : integerCoordinateClaim 172 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_17, phase_linear_6_17, phase_linear_9_17, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_18 : integerCoordinateClaim 172 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_18, phase_linear_6_18, phase_linear_9_18, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_19 : integerCoordinateClaim 172 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_19, phase_linear_6_19, phase_linear_9_19, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_20 : integerCoordinateClaim 172 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_20, phase_linear_6_20, phase_linear_9_20, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_21 : integerCoordinateClaim 172 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_21, phase_linear_6_21, phase_linear_9_21, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_22 : integerCoordinateClaim 172 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_22, phase_linear_6_22, phase_linear_9_22, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

private theorem coordinate_172_23 : integerCoordinateClaim 172 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_172]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_172_0, scale_172_1, scale_172_2, scale_172_3, phase_linear_1_23, phase_linear_6_23, phase_linear_9_23, gram_numerator_literal_6, gram_numerator_literal_31, gram_numerator_literal_42, gram_numerator_literal_118, denominator_literal_172, target_denominator_literal_172, target_numerator_literal_172]
  decide +kernel

theorem integer_residual_172 : integerResidualClaim 172 :=
  (Fin.cases coordinate_172_0 (Fin.cases coordinate_172_1 (Fin.cases coordinate_172_2 (Fin.cases coordinate_172_3 (Fin.cases coordinate_172_4 (Fin.cases coordinate_172_5 (Fin.cases coordinate_172_6 (Fin.cases coordinate_172_7 (Fin.cases coordinate_172_8 (Fin.cases coordinate_172_9 (Fin.cases coordinate_172_10 (Fin.cases coordinate_172_11 (Fin.cases coordinate_172_12 (Fin.cases coordinate_172_13 (Fin.cases coordinate_172_14 (Fin.cases coordinate_172_15 (Fin.cases coordinate_172_16 (Fin.cases coordinate_172_17 (Fin.cases coordinate_172_18 (Fin.cases coordinate_172_19 (Fin.cases coordinate_172_20 (Fin.cases coordinate_172_21 (Fin.cases coordinate_172_22 (Fin.cases coordinate_172_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
