import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear11
import CGLMP5.SOSPhaseLinear14
import CGLMP5.SOSPhaseLinear19

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_120_0 : commonDenominator 120 / (gramDenominator 9 * phaseDenominator 19) = 501845005 := by
  decide +kernel

private theorem scale_120_1 : commonDenominator 120 / (gramDenominator 34 * phaseDenominator 14) = 978728409406056926918912099962962263888535306230093988 := by
  decide +kernel

private theorem scale_120_2 : commonDenominator 120 / (gramDenominator 44 * phaseDenominator 14) = 2 := by
  decide +kernel

private theorem scale_120_3 : commonDenominator 120 / (gramDenominator 112 * phaseDenominator 11) = 501845005 := by
  decide +kernel

theorem denominator_divides_120 : ∀ f ∈ fiber 120, commonDenominator 120 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_120_0 : integerCoordinateClaim 120 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_0, phase_linear_14_0, phase_linear_19_0, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_1 : integerCoordinateClaim 120 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_1, phase_linear_14_1, phase_linear_19_1, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_2 : integerCoordinateClaim 120 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_2, phase_linear_14_2, phase_linear_19_2, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_3 : integerCoordinateClaim 120 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_3, phase_linear_14_3, phase_linear_19_3, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_4 : integerCoordinateClaim 120 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_4, phase_linear_14_4, phase_linear_19_4, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_5 : integerCoordinateClaim 120 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_5, phase_linear_14_5, phase_linear_19_5, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_6 : integerCoordinateClaim 120 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_6, phase_linear_14_6, phase_linear_19_6, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_7 : integerCoordinateClaim 120 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_7, phase_linear_14_7, phase_linear_19_7, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_8 : integerCoordinateClaim 120 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_8, phase_linear_14_8, phase_linear_19_8, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_9 : integerCoordinateClaim 120 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_9, phase_linear_14_9, phase_linear_19_9, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_10 : integerCoordinateClaim 120 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_10, phase_linear_14_10, phase_linear_19_10, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_11 : integerCoordinateClaim 120 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_11, phase_linear_14_11, phase_linear_19_11, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_12 : integerCoordinateClaim 120 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_12, phase_linear_14_12, phase_linear_19_12, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_13 : integerCoordinateClaim 120 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_13, phase_linear_14_13, phase_linear_19_13, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_14 : integerCoordinateClaim 120 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_14, phase_linear_14_14, phase_linear_19_14, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_15 : integerCoordinateClaim 120 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_15, phase_linear_14_15, phase_linear_19_15, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_16 : integerCoordinateClaim 120 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_16, phase_linear_14_16, phase_linear_19_16, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_17 : integerCoordinateClaim 120 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_17, phase_linear_14_17, phase_linear_19_17, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_18 : integerCoordinateClaim 120 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_18, phase_linear_14_18, phase_linear_19_18, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_19 : integerCoordinateClaim 120 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_19, phase_linear_14_19, phase_linear_19_19, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_20 : integerCoordinateClaim 120 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_20, phase_linear_14_20, phase_linear_19_20, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_21 : integerCoordinateClaim 120 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_21, phase_linear_14_21, phase_linear_19_21, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_22 : integerCoordinateClaim 120 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_22, phase_linear_14_22, phase_linear_19_22, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

private theorem coordinate_120_23 : integerCoordinateClaim 120 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_120]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_120_0, scale_120_1, scale_120_2, scale_120_3, phase_linear_11_23, phase_linear_14_23, phase_linear_19_23, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_120, target_denominator_literal_120, target_numerator_literal_120]
  decide +kernel

theorem integer_residual_120 : integerResidualClaim 120 :=
  (Fin.cases coordinate_120_0 (Fin.cases coordinate_120_1 (Fin.cases coordinate_120_2 (Fin.cases coordinate_120_3 (Fin.cases coordinate_120_4 (Fin.cases coordinate_120_5 (Fin.cases coordinate_120_6 (Fin.cases coordinate_120_7 (Fin.cases coordinate_120_8 (Fin.cases coordinate_120_9 (Fin.cases coordinate_120_10 (Fin.cases coordinate_120_11 (Fin.cases coordinate_120_12 (Fin.cases coordinate_120_13 (Fin.cases coordinate_120_14 (Fin.cases coordinate_120_15 (Fin.cases coordinate_120_16 (Fin.cases coordinate_120_17 (Fin.cases coordinate_120_18 (Fin.cases coordinate_120_19 (Fin.cases coordinate_120_20 (Fin.cases coordinate_120_21 (Fin.cases coordinate_120_22 (Fin.cases coordinate_120_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
