import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear03
import CGLMP5.SOSPhaseLinear04

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_112_0 : commonDenominator 112 / (gramDenominator 66 * phaseDenominator 3) = 1 := by
  decide +kernel

private theorem scale_112_1 : commonDenominator 112 / (gramDenominator 73 * phaseDenominator 3) = 1 := by
  decide +kernel

private theorem scale_112_2 : commonDenominator 112 / (gramDenominator 86 * phaseDenominator 4) = 1220801479516445441184408414997261827006880257921711336435147344944888323756402652638225756930017770205778110757103080296531787632388158119592826991087921304175744909670972936872679610 := by
  decide +kernel

theorem denominator_divides_112 : ∀ f ∈ fiber 112, commonDenominator 112 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_112_0 : integerCoordinateClaim 112 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_0, phase_linear_4_0, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_1 : integerCoordinateClaim 112 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_1, phase_linear_4_1, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_2 : integerCoordinateClaim 112 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_2, phase_linear_4_2, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_3 : integerCoordinateClaim 112 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_3, phase_linear_4_3, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_4 : integerCoordinateClaim 112 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_4, phase_linear_4_4, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_5 : integerCoordinateClaim 112 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_5, phase_linear_4_5, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_6 : integerCoordinateClaim 112 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_6, phase_linear_4_6, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_7 : integerCoordinateClaim 112 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_7, phase_linear_4_7, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_8 : integerCoordinateClaim 112 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_8, phase_linear_4_8, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_9 : integerCoordinateClaim 112 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_9, phase_linear_4_9, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_10 : integerCoordinateClaim 112 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_10, phase_linear_4_10, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_11 : integerCoordinateClaim 112 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_11, phase_linear_4_11, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_12 : integerCoordinateClaim 112 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_12, phase_linear_4_12, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_13 : integerCoordinateClaim 112 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_13, phase_linear_4_13, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_14 : integerCoordinateClaim 112 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_14, phase_linear_4_14, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_15 : integerCoordinateClaim 112 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_15, phase_linear_4_15, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_16 : integerCoordinateClaim 112 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_16, phase_linear_4_16, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_17 : integerCoordinateClaim 112 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_17, phase_linear_4_17, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_18 : integerCoordinateClaim 112 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_18, phase_linear_4_18, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_19 : integerCoordinateClaim 112 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_19, phase_linear_4_19, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_20 : integerCoordinateClaim 112 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_20, phase_linear_4_20, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_21 : integerCoordinateClaim 112 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_21, phase_linear_4_21, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_22 : integerCoordinateClaim 112 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_22, phase_linear_4_22, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

private theorem coordinate_112_23 : integerCoordinateClaim 112 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_112]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_112_0, scale_112_1, scale_112_2, phase_linear_3_23, phase_linear_4_23, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_112, target_denominator_literal_112, target_numerator_literal_112]
  decide +kernel

theorem integer_residual_112 : integerResidualClaim 112 :=
  (Fin.cases coordinate_112_0 (Fin.cases coordinate_112_1 (Fin.cases coordinate_112_2 (Fin.cases coordinate_112_3 (Fin.cases coordinate_112_4 (Fin.cases coordinate_112_5 (Fin.cases coordinate_112_6 (Fin.cases coordinate_112_7 (Fin.cases coordinate_112_8 (Fin.cases coordinate_112_9 (Fin.cases coordinate_112_10 (Fin.cases coordinate_112_11 (Fin.cases coordinate_112_12 (Fin.cases coordinate_112_13 (Fin.cases coordinate_112_14 (Fin.cases coordinate_112_15 (Fin.cases coordinate_112_16 (Fin.cases coordinate_112_17 (Fin.cases coordinate_112_18 (Fin.cases coordinate_112_19 (Fin.cases coordinate_112_20 (Fin.cases coordinate_112_21 (Fin.cases coordinate_112_22 (Fin.cases coordinate_112_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
