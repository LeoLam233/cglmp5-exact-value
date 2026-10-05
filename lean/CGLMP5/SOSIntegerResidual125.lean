import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear15
import CGLMP5.SOSPhaseLinear16

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_125_0 : commonDenominator 125 / (gramDenominator 58 * phaseDenominator 15) = 4 := by
  decide +kernel

private theorem scale_125_1 : commonDenominator 125 / (gramDenominator 87 * phaseDenominator 16) = 1 := by
  decide +kernel

theorem denominator_divides_125 : ∀ f ∈ fiber 125, commonDenominator 125 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_125_0 : integerCoordinateClaim 125 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_0, phase_linear_16_0, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_1 : integerCoordinateClaim 125 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_1, phase_linear_16_1, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_2 : integerCoordinateClaim 125 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_2, phase_linear_16_2, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_3 : integerCoordinateClaim 125 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_3, phase_linear_16_3, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_4 : integerCoordinateClaim 125 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_4, phase_linear_16_4, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_5 : integerCoordinateClaim 125 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_5, phase_linear_16_5, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_6 : integerCoordinateClaim 125 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_6, phase_linear_16_6, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_7 : integerCoordinateClaim 125 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_7, phase_linear_16_7, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_8 : integerCoordinateClaim 125 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_8, phase_linear_16_8, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_9 : integerCoordinateClaim 125 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_9, phase_linear_16_9, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_10 : integerCoordinateClaim 125 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_10, phase_linear_16_10, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_11 : integerCoordinateClaim 125 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_11, phase_linear_16_11, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_12 : integerCoordinateClaim 125 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_12, phase_linear_16_12, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_13 : integerCoordinateClaim 125 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_13, phase_linear_16_13, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_14 : integerCoordinateClaim 125 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_14, phase_linear_16_14, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_15 : integerCoordinateClaim 125 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_15, phase_linear_16_15, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_16 : integerCoordinateClaim 125 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_16, phase_linear_16_16, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_17 : integerCoordinateClaim 125 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_17, phase_linear_16_17, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_18 : integerCoordinateClaim 125 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_18, phase_linear_16_18, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_19 : integerCoordinateClaim 125 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_19, phase_linear_16_19, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_20 : integerCoordinateClaim 125 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_20, phase_linear_16_20, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_21 : integerCoordinateClaim 125 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_21, phase_linear_16_21, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_22 : integerCoordinateClaim 125 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_22, phase_linear_16_22, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

private theorem coordinate_125_23 : integerCoordinateClaim 125 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_125]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_125_0, scale_125_1, phase_linear_15_23, phase_linear_16_23, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_125, target_denominator_literal_125, target_numerator_literal_125]
  decide +kernel

theorem integer_residual_125 : integerResidualClaim 125 :=
  (Fin.cases coordinate_125_0 (Fin.cases coordinate_125_1 (Fin.cases coordinate_125_2 (Fin.cases coordinate_125_3 (Fin.cases coordinate_125_4 (Fin.cases coordinate_125_5 (Fin.cases coordinate_125_6 (Fin.cases coordinate_125_7 (Fin.cases coordinate_125_8 (Fin.cases coordinate_125_9 (Fin.cases coordinate_125_10 (Fin.cases coordinate_125_11 (Fin.cases coordinate_125_12 (Fin.cases coordinate_125_13 (Fin.cases coordinate_125_14 (Fin.cases coordinate_125_15 (Fin.cases coordinate_125_16 (Fin.cases coordinate_125_17 (Fin.cases coordinate_125_18 (Fin.cases coordinate_125_19 (Fin.cases coordinate_125_20 (Fin.cases coordinate_125_21 (Fin.cases coordinate_125_22 (Fin.cases coordinate_125_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
