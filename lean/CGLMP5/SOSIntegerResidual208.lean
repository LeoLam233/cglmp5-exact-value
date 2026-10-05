import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear16
import CGLMP5.SOSPhaseLinear17

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_208_0 : commonDenominator 208 / (gramDenominator 69 * phaseDenominator 17) = 1 := by
  decide +kernel

private theorem scale_208_1 : commonDenominator 208 / (gramDenominator 77 * phaseDenominator 17) = 1 := by
  decide +kernel

private theorem scale_208_2 : commonDenominator 208 / (gramDenominator 92 * phaseDenominator 16) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

theorem denominator_divides_208 : ∀ f ∈ fiber 208, commonDenominator 208 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_208_0 : integerCoordinateClaim 208 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_0, phase_linear_17_0, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_1 : integerCoordinateClaim 208 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_1, phase_linear_17_1, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_2 : integerCoordinateClaim 208 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_2, phase_linear_17_2, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_3 : integerCoordinateClaim 208 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_3, phase_linear_17_3, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_4 : integerCoordinateClaim 208 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_4, phase_linear_17_4, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_5 : integerCoordinateClaim 208 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_5, phase_linear_17_5, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_6 : integerCoordinateClaim 208 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_6, phase_linear_17_6, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_7 : integerCoordinateClaim 208 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_7, phase_linear_17_7, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_8 : integerCoordinateClaim 208 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_8, phase_linear_17_8, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_9 : integerCoordinateClaim 208 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_9, phase_linear_17_9, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_10 : integerCoordinateClaim 208 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_10, phase_linear_17_10, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_11 : integerCoordinateClaim 208 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_11, phase_linear_17_11, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_12 : integerCoordinateClaim 208 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_12, phase_linear_17_12, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_13 : integerCoordinateClaim 208 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_13, phase_linear_17_13, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_14 : integerCoordinateClaim 208 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_14, phase_linear_17_14, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_15 : integerCoordinateClaim 208 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_15, phase_linear_17_15, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_16 : integerCoordinateClaim 208 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_16, phase_linear_17_16, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_17 : integerCoordinateClaim 208 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_17, phase_linear_17_17, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_18 : integerCoordinateClaim 208 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_18, phase_linear_17_18, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_19 : integerCoordinateClaim 208 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_19, phase_linear_17_19, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_20 : integerCoordinateClaim 208 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_20, phase_linear_17_20, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_21 : integerCoordinateClaim 208 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_21, phase_linear_17_21, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_22 : integerCoordinateClaim 208 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_22, phase_linear_17_22, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

private theorem coordinate_208_23 : integerCoordinateClaim 208 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_208]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_208_0, scale_208_1, scale_208_2, phase_linear_16_23, phase_linear_17_23, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_208, target_denominator_literal_208, target_numerator_literal_208]
  decide +kernel

theorem integer_residual_208 : integerResidualClaim 208 :=
  (Fin.cases coordinate_208_0 (Fin.cases coordinate_208_1 (Fin.cases coordinate_208_2 (Fin.cases coordinate_208_3 (Fin.cases coordinate_208_4 (Fin.cases coordinate_208_5 (Fin.cases coordinate_208_6 (Fin.cases coordinate_208_7 (Fin.cases coordinate_208_8 (Fin.cases coordinate_208_9 (Fin.cases coordinate_208_10 (Fin.cases coordinate_208_11 (Fin.cases coordinate_208_12 (Fin.cases coordinate_208_13 (Fin.cases coordinate_208_14 (Fin.cases coordinate_208_15 (Fin.cases coordinate_208_16 (Fin.cases coordinate_208_17 (Fin.cases coordinate_208_18 (Fin.cases coordinate_208_19 (Fin.cases coordinate_208_20 (Fin.cases coordinate_208_21 (Fin.cases coordinate_208_22 (Fin.cases coordinate_208_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
