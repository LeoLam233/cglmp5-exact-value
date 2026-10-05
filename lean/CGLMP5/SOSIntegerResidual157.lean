import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear02
import CGLMP5.SOSPhaseLinear12

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_157_0 : commonDenominator 157 / (gramDenominator 65 * phaseDenominator 2) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_157_1 : commonDenominator 157 / (gramDenominator 71 * phaseDenominator 2) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_157_2 : commonDenominator 157 / (gramDenominator 94 * phaseDenominator 12) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

private theorem scale_157_3 : commonDenominator 157 / (gramDenominator 100 * phaseDenominator 12) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

theorem denominator_divides_157 : ∀ f ∈ fiber 157, commonDenominator 157 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_157_0 : integerCoordinateClaim 157 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_0, phase_linear_12_0, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_1 : integerCoordinateClaim 157 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_1, phase_linear_12_1, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_2 : integerCoordinateClaim 157 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_2, phase_linear_12_2, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_3 : integerCoordinateClaim 157 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_3, phase_linear_12_3, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_4 : integerCoordinateClaim 157 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_4, phase_linear_12_4, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_5 : integerCoordinateClaim 157 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_5, phase_linear_12_5, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_6 : integerCoordinateClaim 157 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_6, phase_linear_12_6, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_7 : integerCoordinateClaim 157 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_7, phase_linear_12_7, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_8 : integerCoordinateClaim 157 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_8, phase_linear_12_8, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_9 : integerCoordinateClaim 157 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_9, phase_linear_12_9, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_10 : integerCoordinateClaim 157 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_10, phase_linear_12_10, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_11 : integerCoordinateClaim 157 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_11, phase_linear_12_11, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_12 : integerCoordinateClaim 157 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_12, phase_linear_12_12, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_13 : integerCoordinateClaim 157 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_13, phase_linear_12_13, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_14 : integerCoordinateClaim 157 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_14, phase_linear_12_14, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_15 : integerCoordinateClaim 157 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_15, phase_linear_12_15, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_16 : integerCoordinateClaim 157 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_16, phase_linear_12_16, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_17 : integerCoordinateClaim 157 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_17, phase_linear_12_17, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_18 : integerCoordinateClaim 157 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_18, phase_linear_12_18, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_19 : integerCoordinateClaim 157 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_19, phase_linear_12_19, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_20 : integerCoordinateClaim 157 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_20, phase_linear_12_20, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_21 : integerCoordinateClaim 157 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_21, phase_linear_12_21, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_22 : integerCoordinateClaim 157 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_22, phase_linear_12_22, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

private theorem coordinate_157_23 : integerCoordinateClaim 157 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_157]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_157_0, scale_157_1, scale_157_2, scale_157_3, phase_linear_2_23, phase_linear_12_23, gram_numerator_literal_65, gram_numerator_literal_71, gram_numerator_literal_94, gram_numerator_literal_100, denominator_literal_157, target_denominator_literal_157, target_numerator_literal_157]
  decide +kernel

theorem integer_residual_157 : integerResidualClaim 157 :=
  (Fin.cases coordinate_157_0 (Fin.cases coordinate_157_1 (Fin.cases coordinate_157_2 (Fin.cases coordinate_157_3 (Fin.cases coordinate_157_4 (Fin.cases coordinate_157_5 (Fin.cases coordinate_157_6 (Fin.cases coordinate_157_7 (Fin.cases coordinate_157_8 (Fin.cases coordinate_157_9 (Fin.cases coordinate_157_10 (Fin.cases coordinate_157_11 (Fin.cases coordinate_157_12 (Fin.cases coordinate_157_13 (Fin.cases coordinate_157_14 (Fin.cases coordinate_157_15 (Fin.cases coordinate_157_16 (Fin.cases coordinate_157_17 (Fin.cases coordinate_157_18 (Fin.cases coordinate_157_19 (Fin.cases coordinate_157_20 (Fin.cases coordinate_157_21 (Fin.cases coordinate_157_22 (Fin.cases coordinate_157_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
