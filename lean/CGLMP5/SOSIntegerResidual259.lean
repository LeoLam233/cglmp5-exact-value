import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear15
import CGLMP5.SOSPhaseLinear16

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_259_0 : commonDenominator 259 / (gramDenominator 58 * phaseDenominator 15) = 4 := by
  decide +kernel

private theorem scale_259_1 : commonDenominator 259 / (gramDenominator 87 * phaseDenominator 16) = 1 := by
  decide +kernel

theorem denominator_divides_259 : ∀ f ∈ fiber 259, commonDenominator 259 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_259_0 : integerCoordinateClaim 259 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_0, phase_linear_16_0, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_1 : integerCoordinateClaim 259 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_1, phase_linear_16_1, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_2 : integerCoordinateClaim 259 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_2, phase_linear_16_2, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_3 : integerCoordinateClaim 259 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_3, phase_linear_16_3, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_4 : integerCoordinateClaim 259 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_4, phase_linear_16_4, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_5 : integerCoordinateClaim 259 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_5, phase_linear_16_5, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_6 : integerCoordinateClaim 259 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_6, phase_linear_16_6, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_7 : integerCoordinateClaim 259 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_7, phase_linear_16_7, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_8 : integerCoordinateClaim 259 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_8, phase_linear_16_8, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_9 : integerCoordinateClaim 259 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_9, phase_linear_16_9, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_10 : integerCoordinateClaim 259 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_10, phase_linear_16_10, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_11 : integerCoordinateClaim 259 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_11, phase_linear_16_11, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_12 : integerCoordinateClaim 259 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_12, phase_linear_16_12, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_13 : integerCoordinateClaim 259 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_13, phase_linear_16_13, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_14 : integerCoordinateClaim 259 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_14, phase_linear_16_14, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_15 : integerCoordinateClaim 259 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_15, phase_linear_16_15, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_16 : integerCoordinateClaim 259 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_16, phase_linear_16_16, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_17 : integerCoordinateClaim 259 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_17, phase_linear_16_17, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_18 : integerCoordinateClaim 259 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_18, phase_linear_16_18, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_19 : integerCoordinateClaim 259 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_19, phase_linear_16_19, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_20 : integerCoordinateClaim 259 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_20, phase_linear_16_20, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_21 : integerCoordinateClaim 259 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_21, phase_linear_16_21, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_22 : integerCoordinateClaim 259 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_22, phase_linear_16_22, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

private theorem coordinate_259_23 : integerCoordinateClaim 259 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_259]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_259_0, scale_259_1, phase_linear_15_23, phase_linear_16_23, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_259, target_denominator_literal_259, target_numerator_literal_259]
  decide +kernel

theorem integer_residual_259 : integerResidualClaim 259 :=
  (Fin.cases coordinate_259_0 (Fin.cases coordinate_259_1 (Fin.cases coordinate_259_2 (Fin.cases coordinate_259_3 (Fin.cases coordinate_259_4 (Fin.cases coordinate_259_5 (Fin.cases coordinate_259_6 (Fin.cases coordinate_259_7 (Fin.cases coordinate_259_8 (Fin.cases coordinate_259_9 (Fin.cases coordinate_259_10 (Fin.cases coordinate_259_11 (Fin.cases coordinate_259_12 (Fin.cases coordinate_259_13 (Fin.cases coordinate_259_14 (Fin.cases coordinate_259_15 (Fin.cases coordinate_259_16 (Fin.cases coordinate_259_17 (Fin.cases coordinate_259_18 (Fin.cases coordinate_259_19 (Fin.cases coordinate_259_20 (Fin.cases coordinate_259_21 (Fin.cases coordinate_259_22 (Fin.cases coordinate_259_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
