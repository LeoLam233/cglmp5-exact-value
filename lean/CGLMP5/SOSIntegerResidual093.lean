import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear11
import CGLMP5.SOSPhaseLinear14
import CGLMP5.SOSPhaseLinear19

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_93_0 : commonDenominator 93 / (gramDenominator 9 * phaseDenominator 19) = 501845005 := by
  decide +kernel

private theorem scale_93_1 : commonDenominator 93 / (gramDenominator 34 * phaseDenominator 14) = 978728409406056926918912099962962263888535306230093988 := by
  decide +kernel

private theorem scale_93_2 : commonDenominator 93 / (gramDenominator 44 * phaseDenominator 14) = 2 := by
  decide +kernel

private theorem scale_93_3 : commonDenominator 93 / (gramDenominator 112 * phaseDenominator 11) = 501845005 := by
  decide +kernel

theorem denominator_divides_093 : ∀ f ∈ fiber 93, commonDenominator 93 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_93_0 : integerCoordinateClaim 93 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_0, phase_linear_14_0, phase_linear_19_0, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_1 : integerCoordinateClaim 93 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_1, phase_linear_14_1, phase_linear_19_1, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_2 : integerCoordinateClaim 93 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_2, phase_linear_14_2, phase_linear_19_2, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_3 : integerCoordinateClaim 93 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_3, phase_linear_14_3, phase_linear_19_3, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_4 : integerCoordinateClaim 93 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_4, phase_linear_14_4, phase_linear_19_4, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_5 : integerCoordinateClaim 93 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_5, phase_linear_14_5, phase_linear_19_5, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_6 : integerCoordinateClaim 93 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_6, phase_linear_14_6, phase_linear_19_6, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_7 : integerCoordinateClaim 93 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_7, phase_linear_14_7, phase_linear_19_7, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_8 : integerCoordinateClaim 93 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_8, phase_linear_14_8, phase_linear_19_8, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_9 : integerCoordinateClaim 93 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_9, phase_linear_14_9, phase_linear_19_9, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_10 : integerCoordinateClaim 93 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_10, phase_linear_14_10, phase_linear_19_10, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_11 : integerCoordinateClaim 93 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_11, phase_linear_14_11, phase_linear_19_11, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_12 : integerCoordinateClaim 93 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_12, phase_linear_14_12, phase_linear_19_12, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_13 : integerCoordinateClaim 93 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_13, phase_linear_14_13, phase_linear_19_13, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_14 : integerCoordinateClaim 93 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_14, phase_linear_14_14, phase_linear_19_14, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_15 : integerCoordinateClaim 93 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_15, phase_linear_14_15, phase_linear_19_15, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_16 : integerCoordinateClaim 93 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_16, phase_linear_14_16, phase_linear_19_16, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_17 : integerCoordinateClaim 93 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_17, phase_linear_14_17, phase_linear_19_17, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_18 : integerCoordinateClaim 93 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_18, phase_linear_14_18, phase_linear_19_18, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_19 : integerCoordinateClaim 93 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_19, phase_linear_14_19, phase_linear_19_19, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_20 : integerCoordinateClaim 93 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_20, phase_linear_14_20, phase_linear_19_20, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_21 : integerCoordinateClaim 93 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_21, phase_linear_14_21, phase_linear_19_21, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_22 : integerCoordinateClaim 93 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_22, phase_linear_14_22, phase_linear_19_22, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

private theorem coordinate_93_23 : integerCoordinateClaim 93 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_93]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_93_0, scale_93_1, scale_93_2, scale_93_3, phase_linear_11_23, phase_linear_14_23, phase_linear_19_23, gram_numerator_literal_9, gram_numerator_literal_34, gram_numerator_literal_44, gram_numerator_literal_112, denominator_literal_93, target_denominator_literal_93, target_numerator_literal_93]
  decide +kernel

theorem integer_residual_093 : integerResidualClaim 93 :=
  (Fin.cases coordinate_93_0 (Fin.cases coordinate_93_1 (Fin.cases coordinate_93_2 (Fin.cases coordinate_93_3 (Fin.cases coordinate_93_4 (Fin.cases coordinate_93_5 (Fin.cases coordinate_93_6 (Fin.cases coordinate_93_7 (Fin.cases coordinate_93_8 (Fin.cases coordinate_93_9 (Fin.cases coordinate_93_10 (Fin.cases coordinate_93_11 (Fin.cases coordinate_93_12 (Fin.cases coordinate_93_13 (Fin.cases coordinate_93_14 (Fin.cases coordinate_93_15 (Fin.cases coordinate_93_16 (Fin.cases coordinate_93_17 (Fin.cases coordinate_93_18 (Fin.cases coordinate_93_19 (Fin.cases coordinate_93_20 (Fin.cases coordinate_93_21 (Fin.cases coordinate_93_22 (Fin.cases coordinate_93_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
