import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear03
import CGLMP5.SOSPhaseLinear15
import CGLMP5.SOSPhaseLinear18

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_13_0 : commonDenominator 13 / (gramDenominator 9 * phaseDenominator 3) = 501845005 := by
  decide +kernel

private theorem scale_13_1 : commonDenominator 13 / (gramDenominator 34 * phaseDenominator 18) = 978728409406056926918912099962962263888535306230093988 := by
  decide +kernel

private theorem scale_13_2 : commonDenominator 13 / (gramDenominator 44 * phaseDenominator 18) = 2 := by
  decide +kernel

private theorem scale_13_3 : commonDenominator 13 / (gramDenominator 112 * phaseDenominator 15) = 4014760040 := by
  decide +kernel

theorem denominator_divides_013 : ∀ f ∈ fiber 13, commonDenominator 13 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_13_0 : integerCoordinateClaim 13 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_0, phase_linear_15_0, phase_linear_18_0, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_1 : integerCoordinateClaim 13 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_1, phase_linear_15_1, phase_linear_18_1, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_2 : integerCoordinateClaim 13 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_2, phase_linear_15_2, phase_linear_18_2, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_3 : integerCoordinateClaim 13 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_3, phase_linear_15_3, phase_linear_18_3, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_4 : integerCoordinateClaim 13 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_4, phase_linear_15_4, phase_linear_18_4, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_5 : integerCoordinateClaim 13 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_5, phase_linear_15_5, phase_linear_18_5, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_6 : integerCoordinateClaim 13 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_6, phase_linear_15_6, phase_linear_18_6, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_7 : integerCoordinateClaim 13 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_7, phase_linear_15_7, phase_linear_18_7, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_8 : integerCoordinateClaim 13 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_8, phase_linear_15_8, phase_linear_18_8, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_9 : integerCoordinateClaim 13 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_9, phase_linear_15_9, phase_linear_18_9, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_10 : integerCoordinateClaim 13 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_10, phase_linear_15_10, phase_linear_18_10, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_11 : integerCoordinateClaim 13 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_11, phase_linear_15_11, phase_linear_18_11, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_12 : integerCoordinateClaim 13 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_12, phase_linear_15_12, phase_linear_18_12, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_13 : integerCoordinateClaim 13 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_13, phase_linear_15_13, phase_linear_18_13, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_14 : integerCoordinateClaim 13 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_14, phase_linear_15_14, phase_linear_18_14, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_15 : integerCoordinateClaim 13 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_15, phase_linear_15_15, phase_linear_18_15, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_16 : integerCoordinateClaim 13 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_16, phase_linear_15_16, phase_linear_18_16, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_17 : integerCoordinateClaim 13 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_17, phase_linear_15_17, phase_linear_18_17, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_18 : integerCoordinateClaim 13 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_18, phase_linear_15_18, phase_linear_18_18, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_19 : integerCoordinateClaim 13 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_19, phase_linear_15_19, phase_linear_18_19, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_20 : integerCoordinateClaim 13 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_20, phase_linear_15_20, phase_linear_18_20, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_21 : integerCoordinateClaim 13 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_21, phase_linear_15_21, phase_linear_18_21, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_22 : integerCoordinateClaim 13 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_22, phase_linear_15_22, phase_linear_18_22, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

private theorem coordinate_13_23 : integerCoordinateClaim 13 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_13]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_13_0, scale_13_1, scale_13_2, scale_13_3, phase_linear_3_23, phase_linear_15_23, phase_linear_18_23, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_13, target_denominator_literal_13, target_numerator_literal_13]
  decide +kernel

theorem integer_residual_013 : integerResidualClaim 13 :=
  (Fin.cases coordinate_13_0 (Fin.cases coordinate_13_1 (Fin.cases coordinate_13_2 (Fin.cases coordinate_13_3 (Fin.cases coordinate_13_4 (Fin.cases coordinate_13_5 (Fin.cases coordinate_13_6 (Fin.cases coordinate_13_7 (Fin.cases coordinate_13_8 (Fin.cases coordinate_13_9 (Fin.cases coordinate_13_10 (Fin.cases coordinate_13_11 (Fin.cases coordinate_13_12 (Fin.cases coordinate_13_13 (Fin.cases coordinate_13_14 (Fin.cases coordinate_13_15 (Fin.cases coordinate_13_16 (Fin.cases coordinate_13_17 (Fin.cases coordinate_13_18 (Fin.cases coordinate_13_19 (Fin.cases coordinate_13_20 (Fin.cases coordinate_13_21 (Fin.cases coordinate_13_22 (Fin.cases coordinate_13_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
