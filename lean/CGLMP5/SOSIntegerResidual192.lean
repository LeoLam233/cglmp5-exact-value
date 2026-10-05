import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear03
import CGLMP5.SOSPhaseLinear04

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_192_0 : commonDenominator 192 / (gramDenominator 66 * phaseDenominator 3) = 1 := by
  decide +kernel

private theorem scale_192_1 : commonDenominator 192 / (gramDenominator 73 * phaseDenominator 3) = 1 := by
  decide +kernel

private theorem scale_192_2 : commonDenominator 192 / (gramDenominator 86 * phaseDenominator 4) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

theorem denominator_divides_192 : ∀ f ∈ fiber 192, commonDenominator 192 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_192_0 : integerCoordinateClaim 192 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_0, phase_linear_4_0, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_1 : integerCoordinateClaim 192 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_1, phase_linear_4_1, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_2 : integerCoordinateClaim 192 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_2, phase_linear_4_2, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_3 : integerCoordinateClaim 192 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_3, phase_linear_4_3, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_4 : integerCoordinateClaim 192 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_4, phase_linear_4_4, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_5 : integerCoordinateClaim 192 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_5, phase_linear_4_5, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_6 : integerCoordinateClaim 192 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_6, phase_linear_4_6, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_7 : integerCoordinateClaim 192 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_7, phase_linear_4_7, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_8 : integerCoordinateClaim 192 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_8, phase_linear_4_8, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_9 : integerCoordinateClaim 192 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_9, phase_linear_4_9, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_10 : integerCoordinateClaim 192 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_10, phase_linear_4_10, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_11 : integerCoordinateClaim 192 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_11, phase_linear_4_11, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_12 : integerCoordinateClaim 192 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_12, phase_linear_4_12, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_13 : integerCoordinateClaim 192 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_13, phase_linear_4_13, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_14 : integerCoordinateClaim 192 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_14, phase_linear_4_14, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_15 : integerCoordinateClaim 192 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_15, phase_linear_4_15, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_16 : integerCoordinateClaim 192 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_16, phase_linear_4_16, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_17 : integerCoordinateClaim 192 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_17, phase_linear_4_17, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_18 : integerCoordinateClaim 192 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_18, phase_linear_4_18, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_19 : integerCoordinateClaim 192 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_19, phase_linear_4_19, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_20 : integerCoordinateClaim 192 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_20, phase_linear_4_20, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_21 : integerCoordinateClaim 192 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_21, phase_linear_4_21, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_22 : integerCoordinateClaim 192 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_22, phase_linear_4_22, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

private theorem coordinate_192_23 : integerCoordinateClaim 192 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_192]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_192_0, scale_192_1, scale_192_2, phase_linear_3_23, phase_linear_4_23, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_192, target_denominator_literal_192, target_numerator_literal_192]
  decide +kernel

theorem integer_residual_192 : integerResidualClaim 192 :=
  (Fin.cases coordinate_192_0 (Fin.cases coordinate_192_1 (Fin.cases coordinate_192_2 (Fin.cases coordinate_192_3 (Fin.cases coordinate_192_4 (Fin.cases coordinate_192_5 (Fin.cases coordinate_192_6 (Fin.cases coordinate_192_7 (Fin.cases coordinate_192_8 (Fin.cases coordinate_192_9 (Fin.cases coordinate_192_10 (Fin.cases coordinate_192_11 (Fin.cases coordinate_192_12 (Fin.cases coordinate_192_13 (Fin.cases coordinate_192_14 (Fin.cases coordinate_192_15 (Fin.cases coordinate_192_16 (Fin.cases coordinate_192_17 (Fin.cases coordinate_192_18 (Fin.cases coordinate_192_19 (Fin.cases coordinate_192_20 (Fin.cases coordinate_192_21 (Fin.cases coordinate_192_22 (Fin.cases coordinate_192_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
