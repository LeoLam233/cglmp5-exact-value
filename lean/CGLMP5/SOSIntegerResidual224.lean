import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear00
import CGLMP5.SOSPhaseLinear19

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_224_0 : commonDenominator 224 / (gramDenominator 58 * phaseDenominator 19) = 1 := by
  decide +kernel

private theorem scale_224_1 : commonDenominator 224 / (gramDenominator 87 * phaseDenominator 0) = 4 := by
  decide +kernel

theorem denominator_divides_224 : ∀ f ∈ fiber 224, commonDenominator 224 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_224_0 : integerCoordinateClaim 224 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_0, phase_linear_19_0, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_1 : integerCoordinateClaim 224 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_1, phase_linear_19_1, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_2 : integerCoordinateClaim 224 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_2, phase_linear_19_2, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_3 : integerCoordinateClaim 224 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_3, phase_linear_19_3, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_4 : integerCoordinateClaim 224 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_4, phase_linear_19_4, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_5 : integerCoordinateClaim 224 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_5, phase_linear_19_5, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_6 : integerCoordinateClaim 224 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_6, phase_linear_19_6, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_7 : integerCoordinateClaim 224 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_7, phase_linear_19_7, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_8 : integerCoordinateClaim 224 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_8, phase_linear_19_8, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_9 : integerCoordinateClaim 224 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_9, phase_linear_19_9, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_10 : integerCoordinateClaim 224 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_10, phase_linear_19_10, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_11 : integerCoordinateClaim 224 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_11, phase_linear_19_11, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_12 : integerCoordinateClaim 224 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_12, phase_linear_19_12, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_13 : integerCoordinateClaim 224 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_13, phase_linear_19_13, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_14 : integerCoordinateClaim 224 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_14, phase_linear_19_14, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_15 : integerCoordinateClaim 224 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_15, phase_linear_19_15, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_16 : integerCoordinateClaim 224 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_16, phase_linear_19_16, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_17 : integerCoordinateClaim 224 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_17, phase_linear_19_17, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_18 : integerCoordinateClaim 224 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_18, phase_linear_19_18, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_19 : integerCoordinateClaim 224 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_19, phase_linear_19_19, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_20 : integerCoordinateClaim 224 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_20, phase_linear_19_20, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_21 : integerCoordinateClaim 224 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_21, phase_linear_19_21, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_22 : integerCoordinateClaim 224 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_22, phase_linear_19_22, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

private theorem coordinate_224_23 : integerCoordinateClaim 224 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_224]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_224_0, scale_224_1, phase_linear_0_23, phase_linear_19_23, gram_numerator_literal_58, gram_numerator_literal_87, denominator_literal_224, target_denominator_literal_224, target_numerator_literal_224]
  decide +kernel

theorem integer_residual_224 : integerResidualClaim 224 :=
  (Fin.cases coordinate_224_0 (Fin.cases coordinate_224_1 (Fin.cases coordinate_224_2 (Fin.cases coordinate_224_3 (Fin.cases coordinate_224_4 (Fin.cases coordinate_224_5 (Fin.cases coordinate_224_6 (Fin.cases coordinate_224_7 (Fin.cases coordinate_224_8 (Fin.cases coordinate_224_9 (Fin.cases coordinate_224_10 (Fin.cases coordinate_224_11 (Fin.cases coordinate_224_12 (Fin.cases coordinate_224_13 (Fin.cases coordinate_224_14 (Fin.cases coordinate_224_15 (Fin.cases coordinate_224_16 (Fin.cases coordinate_224_17 (Fin.cases coordinate_224_18 (Fin.cases coordinate_224_19 (Fin.cases coordinate_224_20 (Fin.cases coordinate_224_21 (Fin.cases coordinate_224_22 (Fin.cases coordinate_224_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
