import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear04
import CGLMP5.SOSPhaseLinear14

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_80_0 : commonDenominator 80 / (gramDenominator 65 * phaseDenominator 14) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_80_1 : commonDenominator 80 / (gramDenominator 71 * phaseDenominator 14) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_80_2 : commonDenominator 80 / (gramDenominator 94 * phaseDenominator 4) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

private theorem scale_80_3 : commonDenominator 80 / (gramDenominator 100 * phaseDenominator 4) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

theorem denominator_divides_080 : ∀ f ∈ fiber 80, commonDenominator 80 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_80_0 : integerCoordinateClaim 80 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_0, phase_linear_14_0, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_1 : integerCoordinateClaim 80 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_1, phase_linear_14_1, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_2 : integerCoordinateClaim 80 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_2, phase_linear_14_2, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_3 : integerCoordinateClaim 80 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_3, phase_linear_14_3, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_4 : integerCoordinateClaim 80 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_4, phase_linear_14_4, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_5 : integerCoordinateClaim 80 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_5, phase_linear_14_5, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_6 : integerCoordinateClaim 80 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_6, phase_linear_14_6, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_7 : integerCoordinateClaim 80 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_7, phase_linear_14_7, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_8 : integerCoordinateClaim 80 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_8, phase_linear_14_8, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_9 : integerCoordinateClaim 80 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_9, phase_linear_14_9, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_10 : integerCoordinateClaim 80 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_10, phase_linear_14_10, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_11 : integerCoordinateClaim 80 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_11, phase_linear_14_11, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_12 : integerCoordinateClaim 80 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_12, phase_linear_14_12, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_13 : integerCoordinateClaim 80 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_13, phase_linear_14_13, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_14 : integerCoordinateClaim 80 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_14, phase_linear_14_14, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_15 : integerCoordinateClaim 80 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_15, phase_linear_14_15, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_16 : integerCoordinateClaim 80 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_16, phase_linear_14_16, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_17 : integerCoordinateClaim 80 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_17, phase_linear_14_17, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_18 : integerCoordinateClaim 80 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_18, phase_linear_14_18, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_19 : integerCoordinateClaim 80 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_19, phase_linear_14_19, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_20 : integerCoordinateClaim 80 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_20, phase_linear_14_20, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_21 : integerCoordinateClaim 80 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_21, phase_linear_14_21, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_22 : integerCoordinateClaim 80 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_22, phase_linear_14_22, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

private theorem coordinate_80_23 : integerCoordinateClaim 80 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_80]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_80_0, scale_80_1, scale_80_2, scale_80_3, phase_linear_4_23, phase_linear_14_23, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_80, target_denominator_literal_80, target_numerator_literal_80]
  decide +kernel

theorem integer_residual_080 : integerResidualClaim 80 :=
  (Fin.cases coordinate_80_0 (Fin.cases coordinate_80_1 (Fin.cases coordinate_80_2 (Fin.cases coordinate_80_3 (Fin.cases coordinate_80_4 (Fin.cases coordinate_80_5 (Fin.cases coordinate_80_6 (Fin.cases coordinate_80_7 (Fin.cases coordinate_80_8 (Fin.cases coordinate_80_9 (Fin.cases coordinate_80_10 (Fin.cases coordinate_80_11 (Fin.cases coordinate_80_12 (Fin.cases coordinate_80_13 (Fin.cases coordinate_80_14 (Fin.cases coordinate_80_15 (Fin.cases coordinate_80_16 (Fin.cases coordinate_80_17 (Fin.cases coordinate_80_18 (Fin.cases coordinate_80_19 (Fin.cases coordinate_80_20 (Fin.cases coordinate_80_21 (Fin.cases coordinate_80_22 (Fin.cases coordinate_80_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
