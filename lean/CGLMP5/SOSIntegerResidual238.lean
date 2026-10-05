import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear08
import CGLMP5.SOSPhaseLinear18

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_238_0 : commonDenominator 238 / (gramDenominator 65 * phaseDenominator 18) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_238_1 : commonDenominator 238 / (gramDenominator 71 * phaseDenominator 18) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_238_2 : commonDenominator 238 / (gramDenominator 94 * phaseDenominator 8) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

private theorem scale_238_3 : commonDenominator 238 / (gramDenominator 100 * phaseDenominator 8) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

theorem denominator_divides_238 : ∀ f ∈ fiber 238, commonDenominator 238 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_238_0 : integerCoordinateClaim 238 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_0, phase_linear_18_0, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_1 : integerCoordinateClaim 238 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_1, phase_linear_18_1, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_2 : integerCoordinateClaim 238 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_2, phase_linear_18_2, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_3 : integerCoordinateClaim 238 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_3, phase_linear_18_3, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_4 : integerCoordinateClaim 238 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_4, phase_linear_18_4, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_5 : integerCoordinateClaim 238 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_5, phase_linear_18_5, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_6 : integerCoordinateClaim 238 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_6, phase_linear_18_6, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_7 : integerCoordinateClaim 238 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_7, phase_linear_18_7, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_8 : integerCoordinateClaim 238 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_8, phase_linear_18_8, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_9 : integerCoordinateClaim 238 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_9, phase_linear_18_9, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_10 : integerCoordinateClaim 238 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_10, phase_linear_18_10, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_11 : integerCoordinateClaim 238 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_11, phase_linear_18_11, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_12 : integerCoordinateClaim 238 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_12, phase_linear_18_12, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_13 : integerCoordinateClaim 238 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_13, phase_linear_18_13, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_14 : integerCoordinateClaim 238 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_14, phase_linear_18_14, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_15 : integerCoordinateClaim 238 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_15, phase_linear_18_15, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_16 : integerCoordinateClaim 238 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_16, phase_linear_18_16, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_17 : integerCoordinateClaim 238 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_17, phase_linear_18_17, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_18 : integerCoordinateClaim 238 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_18, phase_linear_18_18, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_19 : integerCoordinateClaim 238 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_19, phase_linear_18_19, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_20 : integerCoordinateClaim 238 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_20, phase_linear_18_20, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_21 : integerCoordinateClaim 238 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_21, phase_linear_18_21, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_22 : integerCoordinateClaim 238 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_22, phase_linear_18_22, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

private theorem coordinate_238_23 : integerCoordinateClaim 238 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_238]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_238_0, scale_238_1, scale_238_2, scale_238_3, phase_linear_8_23, phase_linear_18_23, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_238, target_denominator_literal_238, target_numerator_literal_238]
  decide +kernel

theorem integer_residual_238 : integerResidualClaim 238 :=
  (Fin.cases coordinate_238_0 (Fin.cases coordinate_238_1 (Fin.cases coordinate_238_2 (Fin.cases coordinate_238_3 (Fin.cases coordinate_238_4 (Fin.cases coordinate_238_5 (Fin.cases coordinate_238_6 (Fin.cases coordinate_238_7 (Fin.cases coordinate_238_8 (Fin.cases coordinate_238_9 (Fin.cases coordinate_238_10 (Fin.cases coordinate_238_11 (Fin.cases coordinate_238_12 (Fin.cases coordinate_238_13 (Fin.cases coordinate_238_14 (Fin.cases coordinate_238_15 (Fin.cases coordinate_238_16 (Fin.cases coordinate_238_17 (Fin.cases coordinate_238_18 (Fin.cases coordinate_238_19 (Fin.cases coordinate_238_20 (Fin.cases coordinate_238_21 (Fin.cases coordinate_238_22 (Fin.cases coordinate_238_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
