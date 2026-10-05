import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear03
import CGLMP5.SOSPhaseLinear15
import CGLMP5.SOSPhaseLinear18

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_175_0 : commonDenominator 175 / (gramDenominator 9 * phaseDenominator 3) = 501845005 := by
  decide +kernel

private theorem scale_175_1 : commonDenominator 175 / (gramDenominator 34 * phaseDenominator 18) = 978728409406056926918912099962962263888535306230093988 := by
  decide +kernel

private theorem scale_175_2 : commonDenominator 175 / (gramDenominator 44 * phaseDenominator 18) = 2 := by
  decide +kernel

private theorem scale_175_3 : commonDenominator 175 / (gramDenominator 112 * phaseDenominator 15) = 4014760040 := by
  decide +kernel

theorem denominator_divides_175 : ∀ f ∈ fiber 175, commonDenominator 175 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_175_0 : integerCoordinateClaim 175 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_0, phase_linear_15_0, phase_linear_18_0, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_1 : integerCoordinateClaim 175 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_1, phase_linear_15_1, phase_linear_18_1, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_2 : integerCoordinateClaim 175 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_2, phase_linear_15_2, phase_linear_18_2, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_3 : integerCoordinateClaim 175 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_3, phase_linear_15_3, phase_linear_18_3, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_4 : integerCoordinateClaim 175 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_4, phase_linear_15_4, phase_linear_18_4, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_5 : integerCoordinateClaim 175 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_5, phase_linear_15_5, phase_linear_18_5, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_6 : integerCoordinateClaim 175 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_6, phase_linear_15_6, phase_linear_18_6, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_7 : integerCoordinateClaim 175 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_7, phase_linear_15_7, phase_linear_18_7, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_8 : integerCoordinateClaim 175 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_8, phase_linear_15_8, phase_linear_18_8, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_9 : integerCoordinateClaim 175 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_9, phase_linear_15_9, phase_linear_18_9, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_10 : integerCoordinateClaim 175 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_10, phase_linear_15_10, phase_linear_18_10, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_11 : integerCoordinateClaim 175 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_11, phase_linear_15_11, phase_linear_18_11, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_12 : integerCoordinateClaim 175 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_12, phase_linear_15_12, phase_linear_18_12, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_13 : integerCoordinateClaim 175 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_13, phase_linear_15_13, phase_linear_18_13, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_14 : integerCoordinateClaim 175 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_14, phase_linear_15_14, phase_linear_18_14, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_15 : integerCoordinateClaim 175 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_15, phase_linear_15_15, phase_linear_18_15, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_16 : integerCoordinateClaim 175 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_16, phase_linear_15_16, phase_linear_18_16, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_17 : integerCoordinateClaim 175 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_17, phase_linear_15_17, phase_linear_18_17, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_18 : integerCoordinateClaim 175 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_18, phase_linear_15_18, phase_linear_18_18, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_19 : integerCoordinateClaim 175 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_19, phase_linear_15_19, phase_linear_18_19, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_20 : integerCoordinateClaim 175 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_20, phase_linear_15_20, phase_linear_18_20, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_21 : integerCoordinateClaim 175 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_21, phase_linear_15_21, phase_linear_18_21, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_22 : integerCoordinateClaim 175 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_22, phase_linear_15_22, phase_linear_18_22, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

private theorem coordinate_175_23 : integerCoordinateClaim 175 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_175]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_175_0, scale_175_1, scale_175_2, scale_175_3, phase_linear_3_23, phase_linear_15_23, phase_linear_18_23, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_175, target_denominator_literal_175, target_numerator_literal_175]
  decide +kernel

theorem integer_residual_175 : integerResidualClaim 175 :=
  (Fin.cases coordinate_175_0 (Fin.cases coordinate_175_1 (Fin.cases coordinate_175_2 (Fin.cases coordinate_175_3 (Fin.cases coordinate_175_4 (Fin.cases coordinate_175_5 (Fin.cases coordinate_175_6 (Fin.cases coordinate_175_7 (Fin.cases coordinate_175_8 (Fin.cases coordinate_175_9 (Fin.cases coordinate_175_10 (Fin.cases coordinate_175_11 (Fin.cases coordinate_175_12 (Fin.cases coordinate_175_13 (Fin.cases coordinate_175_14 (Fin.cases coordinate_175_15 (Fin.cases coordinate_175_16 (Fin.cases coordinate_175_17 (Fin.cases coordinate_175_18 (Fin.cases coordinate_175_19 (Fin.cases coordinate_175_20 (Fin.cases coordinate_175_21 (Fin.cases coordinate_175_22 (Fin.cases coordinate_175_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
