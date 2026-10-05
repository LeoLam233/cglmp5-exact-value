import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear04
import CGLMP5.SOSPhaseLinear14

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_186_0 : commonDenominator 186 / (gramDenominator 65 * phaseDenominator 14) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_186_1 : commonDenominator 186 / (gramDenominator 71 * phaseDenominator 14) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_186_2 : commonDenominator 186 / (gramDenominator 94 * phaseDenominator 4) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

private theorem scale_186_3 : commonDenominator 186 / (gramDenominator 100 * phaseDenominator 4) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

theorem denominator_divides_186 : ∀ f ∈ fiber 186, commonDenominator 186 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_186_0 : integerCoordinateClaim 186 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_0, phase_linear_14_0, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_1 : integerCoordinateClaim 186 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_1, phase_linear_14_1, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_2 : integerCoordinateClaim 186 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_2, phase_linear_14_2, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_3 : integerCoordinateClaim 186 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_3, phase_linear_14_3, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_4 : integerCoordinateClaim 186 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_4, phase_linear_14_4, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_5 : integerCoordinateClaim 186 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_5, phase_linear_14_5, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_6 : integerCoordinateClaim 186 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_6, phase_linear_14_6, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_7 : integerCoordinateClaim 186 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_7, phase_linear_14_7, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_8 : integerCoordinateClaim 186 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_8, phase_linear_14_8, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_9 : integerCoordinateClaim 186 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_9, phase_linear_14_9, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_10 : integerCoordinateClaim 186 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_10, phase_linear_14_10, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_11 : integerCoordinateClaim 186 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_11, phase_linear_14_11, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_12 : integerCoordinateClaim 186 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_12, phase_linear_14_12, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_13 : integerCoordinateClaim 186 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_13, phase_linear_14_13, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_14 : integerCoordinateClaim 186 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_14, phase_linear_14_14, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_15 : integerCoordinateClaim 186 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_15, phase_linear_14_15, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_16 : integerCoordinateClaim 186 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_16, phase_linear_14_16, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_17 : integerCoordinateClaim 186 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_17, phase_linear_14_17, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_18 : integerCoordinateClaim 186 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_18, phase_linear_14_18, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_19 : integerCoordinateClaim 186 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_19, phase_linear_14_19, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_20 : integerCoordinateClaim 186 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_20, phase_linear_14_20, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_21 : integerCoordinateClaim 186 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_21, phase_linear_14_21, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_22 : integerCoordinateClaim 186 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_22, phase_linear_14_22, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

private theorem coordinate_186_23 : integerCoordinateClaim 186 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_186]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_186_0, scale_186_1, scale_186_2, scale_186_3, phase_linear_4_23, phase_linear_14_23, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_186, target_denominator_literal_186, target_numerator_literal_186]
  decide +kernel

theorem integer_residual_186 : integerResidualClaim 186 :=
  (Fin.cases coordinate_186_0 (Fin.cases coordinate_186_1 (Fin.cases coordinate_186_2 (Fin.cases coordinate_186_3 (Fin.cases coordinate_186_4 (Fin.cases coordinate_186_5 (Fin.cases coordinate_186_6 (Fin.cases coordinate_186_7 (Fin.cases coordinate_186_8 (Fin.cases coordinate_186_9 (Fin.cases coordinate_186_10 (Fin.cases coordinate_186_11 (Fin.cases coordinate_186_12 (Fin.cases coordinate_186_13 (Fin.cases coordinate_186_14 (Fin.cases coordinate_186_15 (Fin.cases coordinate_186_16 (Fin.cases coordinate_186_17 (Fin.cases coordinate_186_18 (Fin.cases coordinate_186_19 (Fin.cases coordinate_186_20 (Fin.cases coordinate_186_21 (Fin.cases coordinate_186_22 (Fin.cases coordinate_186_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
