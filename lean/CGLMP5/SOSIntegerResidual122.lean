import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear00
import CGLMP5.SOSPhaseLinear19

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_122_0 : commonDenominator 122 / (gramDenominator 58 * phaseDenominator 19) = 1 := by
  decide +kernel

private theorem scale_122_1 : commonDenominator 122 / (gramDenominator 87 * phaseDenominator 0) = 4 := by
  decide +kernel

theorem denominator_divides_122 : ∀ f ∈ fiber 122, commonDenominator 122 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_122_0 : integerCoordinateClaim 122 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_0, phase_linear_19_0, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_1 : integerCoordinateClaim 122 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_1, phase_linear_19_1, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_2 : integerCoordinateClaim 122 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_2, phase_linear_19_2, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_3 : integerCoordinateClaim 122 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_3, phase_linear_19_3, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_4 : integerCoordinateClaim 122 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_4, phase_linear_19_4, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_5 : integerCoordinateClaim 122 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_5, phase_linear_19_5, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_6 : integerCoordinateClaim 122 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_6, phase_linear_19_6, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_7 : integerCoordinateClaim 122 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_7, phase_linear_19_7, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_8 : integerCoordinateClaim 122 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_8, phase_linear_19_8, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_9 : integerCoordinateClaim 122 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_9, phase_linear_19_9, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_10 : integerCoordinateClaim 122 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_10, phase_linear_19_10, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_11 : integerCoordinateClaim 122 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_11, phase_linear_19_11, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_12 : integerCoordinateClaim 122 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_12, phase_linear_19_12, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_13 : integerCoordinateClaim 122 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_13, phase_linear_19_13, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_14 : integerCoordinateClaim 122 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_14, phase_linear_19_14, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_15 : integerCoordinateClaim 122 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_15, phase_linear_19_15, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_16 : integerCoordinateClaim 122 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_16, phase_linear_19_16, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_17 : integerCoordinateClaim 122 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_17, phase_linear_19_17, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_18 : integerCoordinateClaim 122 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_18, phase_linear_19_18, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_19 : integerCoordinateClaim 122 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_19, phase_linear_19_19, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_20 : integerCoordinateClaim 122 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_20, phase_linear_19_20, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_21 : integerCoordinateClaim 122 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_21, phase_linear_19_21, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_22 : integerCoordinateClaim 122 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_22, phase_linear_19_22, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

private theorem coordinate_122_23 : integerCoordinateClaim 122 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_122]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_122_0, scale_122_1, phase_linear_0_23, phase_linear_19_23, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_122, target_denominator_literal_122, target_numerator_literal_122]
  decide +kernel

theorem integer_residual_122 : integerResidualClaim 122 :=
  (Fin.cases coordinate_122_0 (Fin.cases coordinate_122_1 (Fin.cases coordinate_122_2 (Fin.cases coordinate_122_3 (Fin.cases coordinate_122_4 (Fin.cases coordinate_122_5 (Fin.cases coordinate_122_6 (Fin.cases coordinate_122_7 (Fin.cases coordinate_122_8 (Fin.cases coordinate_122_9 (Fin.cases coordinate_122_10 (Fin.cases coordinate_122_11 (Fin.cases coordinate_122_12 (Fin.cases coordinate_122_13 (Fin.cases coordinate_122_14 (Fin.cases coordinate_122_15 (Fin.cases coordinate_122_16 (Fin.cases coordinate_122_17 (Fin.cases coordinate_122_18 (Fin.cases coordinate_122_19 (Fin.cases coordinate_122_20 (Fin.cases coordinate_122_21 (Fin.cases coordinate_122_22 (Fin.cases coordinate_122_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
