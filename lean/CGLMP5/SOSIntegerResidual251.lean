import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear07
import CGLMP5.SOSPhaseLinear08

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_251_0 : commonDenominator 251 / (gramDenominator 58 * phaseDenominator 7) = 1 := by
  decide +kernel

private theorem scale_251_1 : commonDenominator 251 / (gramDenominator 87 * phaseDenominator 8) = 1 := by
  decide +kernel

theorem denominator_divides_251 : ∀ f ∈ fiber 251, commonDenominator 251 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_251_0 : integerCoordinateClaim 251 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_0, phase_linear_8_0, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_1 : integerCoordinateClaim 251 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_1, phase_linear_8_1, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_2 : integerCoordinateClaim 251 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_2, phase_linear_8_2, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_3 : integerCoordinateClaim 251 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_3, phase_linear_8_3, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_4 : integerCoordinateClaim 251 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_4, phase_linear_8_4, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_5 : integerCoordinateClaim 251 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_5, phase_linear_8_5, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_6 : integerCoordinateClaim 251 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_6, phase_linear_8_6, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_7 : integerCoordinateClaim 251 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_7, phase_linear_8_7, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_8 : integerCoordinateClaim 251 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_8, phase_linear_8_8, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_9 : integerCoordinateClaim 251 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_9, phase_linear_8_9, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_10 : integerCoordinateClaim 251 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_10, phase_linear_8_10, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_11 : integerCoordinateClaim 251 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_11, phase_linear_8_11, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_12 : integerCoordinateClaim 251 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_12, phase_linear_8_12, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_13 : integerCoordinateClaim 251 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_13, phase_linear_8_13, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_14 : integerCoordinateClaim 251 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_14, phase_linear_8_14, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_15 : integerCoordinateClaim 251 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_15, phase_linear_8_15, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_16 : integerCoordinateClaim 251 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_16, phase_linear_8_16, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_17 : integerCoordinateClaim 251 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_17, phase_linear_8_17, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_18 : integerCoordinateClaim 251 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_18, phase_linear_8_18, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_19 : integerCoordinateClaim 251 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_19, phase_linear_8_19, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_20 : integerCoordinateClaim 251 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_20, phase_linear_8_20, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_21 : integerCoordinateClaim 251 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_21, phase_linear_8_21, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_22 : integerCoordinateClaim 251 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_22, phase_linear_8_22, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

private theorem coordinate_251_23 : integerCoordinateClaim 251 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_251]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_251_0, scale_251_1, phase_linear_7_23, phase_linear_8_23, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_251, target_denominator_literal_251, target_numerator_literal_251]
  decide +kernel

theorem integer_residual_251 : integerResidualClaim 251 :=
  (Fin.cases coordinate_251_0 (Fin.cases coordinate_251_1 (Fin.cases coordinate_251_2 (Fin.cases coordinate_251_3 (Fin.cases coordinate_251_4 (Fin.cases coordinate_251_5 (Fin.cases coordinate_251_6 (Fin.cases coordinate_251_7 (Fin.cases coordinate_251_8 (Fin.cases coordinate_251_9 (Fin.cases coordinate_251_10 (Fin.cases coordinate_251_11 (Fin.cases coordinate_251_12 (Fin.cases coordinate_251_13 (Fin.cases coordinate_251_14 (Fin.cases coordinate_251_15 (Fin.cases coordinate_251_16 (Fin.cases coordinate_251_17 (Fin.cases coordinate_251_18 (Fin.cases coordinate_251_19 (Fin.cases coordinate_251_20 (Fin.cases coordinate_251_21 (Fin.cases coordinate_251_22 (Fin.cases coordinate_251_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
