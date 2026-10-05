import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear08
import CGLMP5.SOSPhaseLinear18

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_28_0 : commonDenominator 28 / (gramDenominator 65 * phaseDenominator 18) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_28_1 : commonDenominator 28 / (gramDenominator 71 * phaseDenominator 18) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_28_2 : commonDenominator 28 / (gramDenominator 94 * phaseDenominator 8) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

private theorem scale_28_3 : commonDenominator 28 / (gramDenominator 100 * phaseDenominator 8) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

theorem denominator_divides_028 : ∀ f ∈ fiber 28, commonDenominator 28 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_28_0 : integerCoordinateClaim 28 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_0, phase_linear_18_0, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_1 : integerCoordinateClaim 28 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_1, phase_linear_18_1, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_2 : integerCoordinateClaim 28 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_2, phase_linear_18_2, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_3 : integerCoordinateClaim 28 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_3, phase_linear_18_3, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_4 : integerCoordinateClaim 28 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_4, phase_linear_18_4, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_5 : integerCoordinateClaim 28 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_5, phase_linear_18_5, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_6 : integerCoordinateClaim 28 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_6, phase_linear_18_6, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_7 : integerCoordinateClaim 28 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_7, phase_linear_18_7, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_8 : integerCoordinateClaim 28 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_8, phase_linear_18_8, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_9 : integerCoordinateClaim 28 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_9, phase_linear_18_9, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_10 : integerCoordinateClaim 28 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_10, phase_linear_18_10, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_11 : integerCoordinateClaim 28 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_11, phase_linear_18_11, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_12 : integerCoordinateClaim 28 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_12, phase_linear_18_12, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_13 : integerCoordinateClaim 28 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_13, phase_linear_18_13, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_14 : integerCoordinateClaim 28 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_14, phase_linear_18_14, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_15 : integerCoordinateClaim 28 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_15, phase_linear_18_15, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_16 : integerCoordinateClaim 28 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_16, phase_linear_18_16, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_17 : integerCoordinateClaim 28 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_17, phase_linear_18_17, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_18 : integerCoordinateClaim 28 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_18, phase_linear_18_18, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_19 : integerCoordinateClaim 28 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_19, phase_linear_18_19, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_20 : integerCoordinateClaim 28 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_20, phase_linear_18_20, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_21 : integerCoordinateClaim 28 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_21, phase_linear_18_21, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_22 : integerCoordinateClaim 28 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_22, phase_linear_18_22, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

private theorem coordinate_28_23 : integerCoordinateClaim 28 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_28]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_28_0, scale_28_1, scale_28_2, scale_28_3, phase_linear_8_23, phase_linear_18_23, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_28, target_denominator_literal_28, target_numerator_literal_28]
  decide +kernel

theorem integer_residual_028 : integerResidualClaim 28 :=
  (Fin.cases coordinate_28_0 (Fin.cases coordinate_28_1 (Fin.cases coordinate_28_2 (Fin.cases coordinate_28_3 (Fin.cases coordinate_28_4 (Fin.cases coordinate_28_5 (Fin.cases coordinate_28_6 (Fin.cases coordinate_28_7 (Fin.cases coordinate_28_8 (Fin.cases coordinate_28_9 (Fin.cases coordinate_28_10 (Fin.cases coordinate_28_11 (Fin.cases coordinate_28_12 (Fin.cases coordinate_28_13 (Fin.cases coordinate_28_14 (Fin.cases coordinate_28_15 (Fin.cases coordinate_28_16 (Fin.cases coordinate_28_17 (Fin.cases coordinate_28_18 (Fin.cases coordinate_28_19 (Fin.cases coordinate_28_20 (Fin.cases coordinate_28_21 (Fin.cases coordinate_28_22 (Fin.cases coordinate_28_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
