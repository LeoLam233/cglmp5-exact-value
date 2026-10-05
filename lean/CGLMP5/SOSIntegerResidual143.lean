import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear12
import CGLMP5.SOSPhaseLinear13

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_143_0 : commonDenominator 143 / (gramDenominator 67 * phaseDenominator 13) = 1 := by
  decide +kernel

private theorem scale_143_1 : commonDenominator 143 / (gramDenominator 96 * phaseDenominator 12) = 1 := by
  decide +kernel

theorem denominator_divides_143 : ∀ f ∈ fiber 143, commonDenominator 143 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_143_0 : integerCoordinateClaim 143 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_0, phase_linear_13_0, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_1 : integerCoordinateClaim 143 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_1, phase_linear_13_1, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_2 : integerCoordinateClaim 143 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_2, phase_linear_13_2, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_3 : integerCoordinateClaim 143 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_3, phase_linear_13_3, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_4 : integerCoordinateClaim 143 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_4, phase_linear_13_4, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_5 : integerCoordinateClaim 143 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_5, phase_linear_13_5, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_6 : integerCoordinateClaim 143 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_6, phase_linear_13_6, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_7 : integerCoordinateClaim 143 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_7, phase_linear_13_7, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_8 : integerCoordinateClaim 143 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_8, phase_linear_13_8, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_9 : integerCoordinateClaim 143 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_9, phase_linear_13_9, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_10 : integerCoordinateClaim 143 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_10, phase_linear_13_10, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_11 : integerCoordinateClaim 143 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_11, phase_linear_13_11, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_12 : integerCoordinateClaim 143 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_12, phase_linear_13_12, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_13 : integerCoordinateClaim 143 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_13, phase_linear_13_13, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_14 : integerCoordinateClaim 143 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_14, phase_linear_13_14, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_15 : integerCoordinateClaim 143 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_15, phase_linear_13_15, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_16 : integerCoordinateClaim 143 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_16, phase_linear_13_16, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_17 : integerCoordinateClaim 143 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_17, phase_linear_13_17, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_18 : integerCoordinateClaim 143 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_18, phase_linear_13_18, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_19 : integerCoordinateClaim 143 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_19, phase_linear_13_19, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_20 : integerCoordinateClaim 143 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_20, phase_linear_13_20, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_21 : integerCoordinateClaim 143 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_21, phase_linear_13_21, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_22 : integerCoordinateClaim 143 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_22, phase_linear_13_22, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

private theorem coordinate_143_23 : integerCoordinateClaim 143 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_143]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_143_0, scale_143_1, phase_linear_12_23, phase_linear_13_23, gram_numerator_literal_67, gram_numerator_literal_96, denominator_literal_143, target_denominator_literal_143, target_numerator_literal_143]
  decide +kernel

theorem integer_residual_143 : integerResidualClaim 143 :=
  (Fin.cases coordinate_143_0 (Fin.cases coordinate_143_1 (Fin.cases coordinate_143_2 (Fin.cases coordinate_143_3 (Fin.cases coordinate_143_4 (Fin.cases coordinate_143_5 (Fin.cases coordinate_143_6 (Fin.cases coordinate_143_7 (Fin.cases coordinate_143_8 (Fin.cases coordinate_143_9 (Fin.cases coordinate_143_10 (Fin.cases coordinate_143_11 (Fin.cases coordinate_143_12 (Fin.cases coordinate_143_13 (Fin.cases coordinate_143_14 (Fin.cases coordinate_143_15 (Fin.cases coordinate_143_16 (Fin.cases coordinate_143_17 (Fin.cases coordinate_143_18 (Fin.cases coordinate_143_19 (Fin.cases coordinate_143_20 (Fin.cases coordinate_143_21 (Fin.cases coordinate_143_22 (Fin.cases coordinate_143_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
