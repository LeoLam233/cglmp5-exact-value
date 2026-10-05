import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear06
import CGLMP5.SOSPhaseLinear16

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_215_0 : commonDenominator 215 / (gramDenominator 65 * phaseDenominator 6) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_215_1 : commonDenominator 215 / (gramDenominator 71 * phaseDenominator 6) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_215_2 : commonDenominator 215 / (gramDenominator 94 * phaseDenominator 16) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

private theorem scale_215_3 : commonDenominator 215 / (gramDenominator 100 * phaseDenominator 16) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

theorem denominator_divides_215 : ∀ f ∈ fiber 215, commonDenominator 215 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_215_0 : integerCoordinateClaim 215 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_0, phase_linear_16_0, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_1 : integerCoordinateClaim 215 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_1, phase_linear_16_1, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_2 : integerCoordinateClaim 215 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_2, phase_linear_16_2, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_3 : integerCoordinateClaim 215 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_3, phase_linear_16_3, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_4 : integerCoordinateClaim 215 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_4, phase_linear_16_4, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_5 : integerCoordinateClaim 215 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_5, phase_linear_16_5, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_6 : integerCoordinateClaim 215 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_6, phase_linear_16_6, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_7 : integerCoordinateClaim 215 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_7, phase_linear_16_7, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_8 : integerCoordinateClaim 215 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_8, phase_linear_16_8, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_9 : integerCoordinateClaim 215 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_9, phase_linear_16_9, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_10 : integerCoordinateClaim 215 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_10, phase_linear_16_10, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_11 : integerCoordinateClaim 215 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_11, phase_linear_16_11, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_12 : integerCoordinateClaim 215 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_12, phase_linear_16_12, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_13 : integerCoordinateClaim 215 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_13, phase_linear_16_13, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_14 : integerCoordinateClaim 215 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_14, phase_linear_16_14, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_15 : integerCoordinateClaim 215 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_15, phase_linear_16_15, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_16 : integerCoordinateClaim 215 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_16, phase_linear_16_16, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_17 : integerCoordinateClaim 215 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_17, phase_linear_16_17, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_18 : integerCoordinateClaim 215 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_18, phase_linear_16_18, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_19 : integerCoordinateClaim 215 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_19, phase_linear_16_19, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_20 : integerCoordinateClaim 215 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_20, phase_linear_16_20, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_21 : integerCoordinateClaim 215 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_21, phase_linear_16_21, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_22 : integerCoordinateClaim 215 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_22, phase_linear_16_22, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

private theorem coordinate_215_23 : integerCoordinateClaim 215 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_215]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_215_0, scale_215_1, scale_215_2, scale_215_3, phase_linear_6_23, phase_linear_16_23, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_215, target_denominator_literal_215, target_numerator_literal_215]
  decide +kernel

theorem integer_residual_215 : integerResidualClaim 215 :=
  (Fin.cases coordinate_215_0 (Fin.cases coordinate_215_1 (Fin.cases coordinate_215_2 (Fin.cases coordinate_215_3 (Fin.cases coordinate_215_4 (Fin.cases coordinate_215_5 (Fin.cases coordinate_215_6 (Fin.cases coordinate_215_7 (Fin.cases coordinate_215_8 (Fin.cases coordinate_215_9 (Fin.cases coordinate_215_10 (Fin.cases coordinate_215_11 (Fin.cases coordinate_215_12 (Fin.cases coordinate_215_13 (Fin.cases coordinate_215_14 (Fin.cases coordinate_215_15 (Fin.cases coordinate_215_16 (Fin.cases coordinate_215_17 (Fin.cases coordinate_215_18 (Fin.cases coordinate_215_19 (Fin.cases coordinate_215_20 (Fin.cases coordinate_215_21 (Fin.cases coordinate_215_22 (Fin.cases coordinate_215_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
