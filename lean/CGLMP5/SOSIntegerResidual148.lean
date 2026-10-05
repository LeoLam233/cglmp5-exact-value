import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear02
import CGLMP5.SOSPhaseLinear07
import CGLMP5.SOSPhaseLinear19

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_148_0 : commonDenominator 148 / (gramDenominator 9 * phaseDenominator 7) = 501845005 := by
  decide +kernel

private theorem scale_148_1 : commonDenominator 148 / (gramDenominator 34 * phaseDenominator 2) = 978728409406056926918912099962962263888535306230093988 := by
  decide +kernel

private theorem scale_148_2 : commonDenominator 148 / (gramDenominator 44 * phaseDenominator 2) = 2 := by
  decide +kernel

private theorem scale_148_3 : commonDenominator 148 / (gramDenominator 112 * phaseDenominator 19) = 1003690010 := by
  decide +kernel

theorem denominator_divides_148 : ∀ f ∈ fiber 148, commonDenominator 148 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_148_0 : integerCoordinateClaim 148 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_0, phase_linear_7_0, phase_linear_19_0, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_1 : integerCoordinateClaim 148 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_1, phase_linear_7_1, phase_linear_19_1, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_2 : integerCoordinateClaim 148 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_2, phase_linear_7_2, phase_linear_19_2, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_3 : integerCoordinateClaim 148 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_3, phase_linear_7_3, phase_linear_19_3, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_4 : integerCoordinateClaim 148 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_4, phase_linear_7_4, phase_linear_19_4, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_5 : integerCoordinateClaim 148 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_5, phase_linear_7_5, phase_linear_19_5, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_6 : integerCoordinateClaim 148 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_6, phase_linear_7_6, phase_linear_19_6, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_7 : integerCoordinateClaim 148 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_7, phase_linear_7_7, phase_linear_19_7, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_8 : integerCoordinateClaim 148 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_8, phase_linear_7_8, phase_linear_19_8, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_9 : integerCoordinateClaim 148 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_9, phase_linear_7_9, phase_linear_19_9, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_10 : integerCoordinateClaim 148 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_10, phase_linear_7_10, phase_linear_19_10, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_11 : integerCoordinateClaim 148 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_11, phase_linear_7_11, phase_linear_19_11, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_12 : integerCoordinateClaim 148 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_12, phase_linear_7_12, phase_linear_19_12, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_13 : integerCoordinateClaim 148 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_13, phase_linear_7_13, phase_linear_19_13, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_14 : integerCoordinateClaim 148 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_14, phase_linear_7_14, phase_linear_19_14, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_15 : integerCoordinateClaim 148 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_15, phase_linear_7_15, phase_linear_19_15, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_16 : integerCoordinateClaim 148 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_16, phase_linear_7_16, phase_linear_19_16, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_17 : integerCoordinateClaim 148 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_17, phase_linear_7_17, phase_linear_19_17, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_18 : integerCoordinateClaim 148 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_18, phase_linear_7_18, phase_linear_19_18, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_19 : integerCoordinateClaim 148 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_19, phase_linear_7_19, phase_linear_19_19, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_20 : integerCoordinateClaim 148 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_20, phase_linear_7_20, phase_linear_19_20, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_21 : integerCoordinateClaim 148 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_21, phase_linear_7_21, phase_linear_19_21, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_22 : integerCoordinateClaim 148 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_22, phase_linear_7_22, phase_linear_19_22, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

private theorem coordinate_148_23 : integerCoordinateClaim 148 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_148]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_148_0, scale_148_1, scale_148_2, scale_148_3, phase_linear_2_23, phase_linear_7_23, phase_linear_19_23, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_148, target_denominator_literal_148, target_numerator_literal_148]
  decide +kernel

theorem integer_residual_148 : integerResidualClaim 148 :=
  (Fin.cases coordinate_148_0 (Fin.cases coordinate_148_1 (Fin.cases coordinate_148_2 (Fin.cases coordinate_148_3 (Fin.cases coordinate_148_4 (Fin.cases coordinate_148_5 (Fin.cases coordinate_148_6 (Fin.cases coordinate_148_7 (Fin.cases coordinate_148_8 (Fin.cases coordinate_148_9 (Fin.cases coordinate_148_10 (Fin.cases coordinate_148_11 (Fin.cases coordinate_148_12 (Fin.cases coordinate_148_13 (Fin.cases coordinate_148_14 (Fin.cases coordinate_148_15 (Fin.cases coordinate_148_16 (Fin.cases coordinate_148_17 (Fin.cases coordinate_148_18 (Fin.cases coordinate_148_19 (Fin.cases coordinate_148_20 (Fin.cases coordinate_148_21 (Fin.cases coordinate_148_22 (Fin.cases coordinate_148_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
