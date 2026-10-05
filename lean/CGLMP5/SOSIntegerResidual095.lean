import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear07
import CGLMP5.SOSPhaseLinear08

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_95_0 : commonDenominator 95 / (gramDenominator 58 * phaseDenominator 7) = 1 := by
  decide +kernel

private theorem scale_95_1 : commonDenominator 95 / (gramDenominator 87 * phaseDenominator 8) = 1 := by
  decide +kernel

theorem denominator_divides_095 : ∀ f ∈ fiber 95, commonDenominator 95 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_95_0 : integerCoordinateClaim 95 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_0, phase_linear_8_0, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_1 : integerCoordinateClaim 95 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_1, phase_linear_8_1, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_2 : integerCoordinateClaim 95 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_2, phase_linear_8_2, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_3 : integerCoordinateClaim 95 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_3, phase_linear_8_3, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_4 : integerCoordinateClaim 95 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_4, phase_linear_8_4, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_5 : integerCoordinateClaim 95 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_5, phase_linear_8_5, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_6 : integerCoordinateClaim 95 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_6, phase_linear_8_6, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_7 : integerCoordinateClaim 95 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_7, phase_linear_8_7, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_8 : integerCoordinateClaim 95 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_8, phase_linear_8_8, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_9 : integerCoordinateClaim 95 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_9, phase_linear_8_9, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_10 : integerCoordinateClaim 95 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_10, phase_linear_8_10, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_11 : integerCoordinateClaim 95 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_11, phase_linear_8_11, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_12 : integerCoordinateClaim 95 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_12, phase_linear_8_12, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_13 : integerCoordinateClaim 95 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_13, phase_linear_8_13, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_14 : integerCoordinateClaim 95 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_14, phase_linear_8_14, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_15 : integerCoordinateClaim 95 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_15, phase_linear_8_15, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_16 : integerCoordinateClaim 95 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_16, phase_linear_8_16, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_17 : integerCoordinateClaim 95 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_17, phase_linear_8_17, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_18 : integerCoordinateClaim 95 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_18, phase_linear_8_18, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_19 : integerCoordinateClaim 95 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_19, phase_linear_8_19, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_20 : integerCoordinateClaim 95 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_20, phase_linear_8_20, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_21 : integerCoordinateClaim 95 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_21, phase_linear_8_21, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_22 : integerCoordinateClaim 95 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_22, phase_linear_8_22, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

private theorem coordinate_95_23 : integerCoordinateClaim 95 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_95]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_95_0, scale_95_1, phase_linear_7_23, phase_linear_8_23, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_95, target_denominator_literal_95, target_numerator_literal_95]
  decide +kernel

theorem integer_residual_095 : integerResidualClaim 95 :=
  (Fin.cases coordinate_95_0 (Fin.cases coordinate_95_1 (Fin.cases coordinate_95_2 (Fin.cases coordinate_95_3 (Fin.cases coordinate_95_4 (Fin.cases coordinate_95_5 (Fin.cases coordinate_95_6 (Fin.cases coordinate_95_7 (Fin.cases coordinate_95_8 (Fin.cases coordinate_95_9 (Fin.cases coordinate_95_10 (Fin.cases coordinate_95_11 (Fin.cases coordinate_95_12 (Fin.cases coordinate_95_13 (Fin.cases coordinate_95_14 (Fin.cases coordinate_95_15 (Fin.cases coordinate_95_16 (Fin.cases coordinate_95_17 (Fin.cases coordinate_95_18 (Fin.cases coordinate_95_19 (Fin.cases coordinate_95_20 (Fin.cases coordinate_95_21 (Fin.cases coordinate_95_22 (Fin.cases coordinate_95_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
