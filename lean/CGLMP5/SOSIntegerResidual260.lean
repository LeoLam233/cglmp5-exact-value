import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear03
import CGLMP5.SOSPhaseLinear04

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_260_0 : commonDenominator 260 / (gramDenominator 58 * phaseDenominator 3) = 1 := by
  decide +kernel

private theorem scale_260_1 : commonDenominator 260 / (gramDenominator 87 * phaseDenominator 4) = 2 := by
  decide +kernel

theorem denominator_divides_260 : ∀ f ∈ fiber 260, commonDenominator 260 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_260_0 : integerCoordinateClaim 260 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_0, phase_linear_4_0, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_1 : integerCoordinateClaim 260 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_1, phase_linear_4_1, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_2 : integerCoordinateClaim 260 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_2, phase_linear_4_2, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_3 : integerCoordinateClaim 260 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_3, phase_linear_4_3, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_4 : integerCoordinateClaim 260 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_4, phase_linear_4_4, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_5 : integerCoordinateClaim 260 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_5, phase_linear_4_5, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_6 : integerCoordinateClaim 260 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_6, phase_linear_4_6, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_7 : integerCoordinateClaim 260 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_7, phase_linear_4_7, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_8 : integerCoordinateClaim 260 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_8, phase_linear_4_8, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_9 : integerCoordinateClaim 260 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_9, phase_linear_4_9, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_10 : integerCoordinateClaim 260 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_10, phase_linear_4_10, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_11 : integerCoordinateClaim 260 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_11, phase_linear_4_11, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_12 : integerCoordinateClaim 260 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_12, phase_linear_4_12, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_13 : integerCoordinateClaim 260 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_13, phase_linear_4_13, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_14 : integerCoordinateClaim 260 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_14, phase_linear_4_14, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_15 : integerCoordinateClaim 260 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_15, phase_linear_4_15, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_16 : integerCoordinateClaim 260 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_16, phase_linear_4_16, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_17 : integerCoordinateClaim 260 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_17, phase_linear_4_17, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_18 : integerCoordinateClaim 260 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_18, phase_linear_4_18, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_19 : integerCoordinateClaim 260 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_19, phase_linear_4_19, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_20 : integerCoordinateClaim 260 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_20, phase_linear_4_20, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_21 : integerCoordinateClaim 260 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_21, phase_linear_4_21, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_22 : integerCoordinateClaim 260 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_22, phase_linear_4_22, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

private theorem coordinate_260_23 : integerCoordinateClaim 260 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_260]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_260_0, scale_260_1, phase_linear_3_23, phase_linear_4_23, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_260, target_denominator_literal_260, target_numerator_literal_260]
  decide +kernel

theorem integer_residual_260 : integerResidualClaim 260 :=
  (Fin.cases coordinate_260_0 (Fin.cases coordinate_260_1 (Fin.cases coordinate_260_2 (Fin.cases coordinate_260_3 (Fin.cases coordinate_260_4 (Fin.cases coordinate_260_5 (Fin.cases coordinate_260_6 (Fin.cases coordinate_260_7 (Fin.cases coordinate_260_8 (Fin.cases coordinate_260_9 (Fin.cases coordinate_260_10 (Fin.cases coordinate_260_11 (Fin.cases coordinate_260_12 (Fin.cases coordinate_260_13 (Fin.cases coordinate_260_14 (Fin.cases coordinate_260_15 (Fin.cases coordinate_260_16 (Fin.cases coordinate_260_17 (Fin.cases coordinate_260_18 (Fin.cases coordinate_260_19 (Fin.cases coordinate_260_20 (Fin.cases coordinate_260_21 (Fin.cases coordinate_260_22 (Fin.cases coordinate_260_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
