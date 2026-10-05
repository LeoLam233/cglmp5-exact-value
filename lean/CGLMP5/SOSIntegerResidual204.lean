import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear06
import CGLMP5.SOSPhaseLinear09
import CGLMP5.SOSPhaseLinear16

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_204_0 : commonDenominator 204 / (gramDenominator 7 * phaseDenominator 6) = 100369001 := by
  decide +kernel

private theorem scale_204_1 : commonDenominator 204 / (gramDenominator 22 * phaseDenominator 6) = 100369001 := by
  decide +kernel

private theorem scale_204_2 : commonDenominator 204 / (gramDenominator 32 * phaseDenominator 16) = 565067391620740610795147924603265531283049210333352616015406684909221111333511442266879382553950000665889099736745355550891914359077178480461644492096344976413153749392572285307303092265466068243718181033374379403937004785940629244085093440831076285959077920 := by
  decide +kernel

private theorem scale_204_3 : commonDenominator 204 / (gramDenominator 43 * phaseDenominator 16) = 8877811354540343962614524755626817296347346612184603591684633258150591283269387781385071061580871176509056413622582853752873595962424774696622245576048504735999004421861266385365838 := by
  decide +kernel

private theorem scale_204_4 : commonDenominator 204 / (gramDenominator 122 * phaseDenominator 9) = 445528528360835568862000598906016390421952064232851545039199273585974977330528232749612989382440760347954329843970716035452511853013104086975026431422328973947994405408398933847025089793919 := by
  decide +kernel

theorem denominator_divides_204 : ∀ f ∈ fiber 204, commonDenominator 204 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_204_0 : integerCoordinateClaim 204 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_0, phase_linear_9_0, phase_linear_16_0, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_1 : integerCoordinateClaim 204 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_1, phase_linear_9_1, phase_linear_16_1, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_2 : integerCoordinateClaim 204 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_2, phase_linear_9_2, phase_linear_16_2, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_3 : integerCoordinateClaim 204 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_3, phase_linear_9_3, phase_linear_16_3, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_4 : integerCoordinateClaim 204 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_4, phase_linear_9_4, phase_linear_16_4, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_5 : integerCoordinateClaim 204 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_5, phase_linear_9_5, phase_linear_16_5, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_6 : integerCoordinateClaim 204 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_6, phase_linear_9_6, phase_linear_16_6, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_7 : integerCoordinateClaim 204 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_7, phase_linear_9_7, phase_linear_16_7, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_8 : integerCoordinateClaim 204 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_8, phase_linear_9_8, phase_linear_16_8, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_9 : integerCoordinateClaim 204 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_9, phase_linear_9_9, phase_linear_16_9, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_10 : integerCoordinateClaim 204 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_10, phase_linear_9_10, phase_linear_16_10, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_11 : integerCoordinateClaim 204 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_11, phase_linear_9_11, phase_linear_16_11, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_12 : integerCoordinateClaim 204 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_12, phase_linear_9_12, phase_linear_16_12, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_13 : integerCoordinateClaim 204 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_13, phase_linear_9_13, phase_linear_16_13, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_14 : integerCoordinateClaim 204 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_14, phase_linear_9_14, phase_linear_16_14, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_15 : integerCoordinateClaim 204 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_15, phase_linear_9_15, phase_linear_16_15, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_16 : integerCoordinateClaim 204 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_16, phase_linear_9_16, phase_linear_16_16, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_17 : integerCoordinateClaim 204 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_17, phase_linear_9_17, phase_linear_16_17, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_18 : integerCoordinateClaim 204 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_18, phase_linear_9_18, phase_linear_16_18, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_19 : integerCoordinateClaim 204 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_19, phase_linear_9_19, phase_linear_16_19, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_20 : integerCoordinateClaim 204 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_20, phase_linear_9_20, phase_linear_16_20, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_21 : integerCoordinateClaim 204 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_21, phase_linear_9_21, phase_linear_16_21, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_22 : integerCoordinateClaim 204 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_22, phase_linear_9_22, phase_linear_16_22, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

private theorem coordinate_204_23 : integerCoordinateClaim 204 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_204]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_204_0, scale_204_1, scale_204_2, scale_204_3, scale_204_4, phase_linear_6_23, phase_linear_9_23, phase_linear_16_23, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_204, target_denominator_literal_204, target_numerator_literal_204]
  decide +kernel

theorem integer_residual_204 : integerResidualClaim 204 :=
  (Fin.cases coordinate_204_0 (Fin.cases coordinate_204_1 (Fin.cases coordinate_204_2 (Fin.cases coordinate_204_3 (Fin.cases coordinate_204_4 (Fin.cases coordinate_204_5 (Fin.cases coordinate_204_6 (Fin.cases coordinate_204_7 (Fin.cases coordinate_204_8 (Fin.cases coordinate_204_9 (Fin.cases coordinate_204_10 (Fin.cases coordinate_204_11 (Fin.cases coordinate_204_12 (Fin.cases coordinate_204_13 (Fin.cases coordinate_204_14 (Fin.cases coordinate_204_15 (Fin.cases coordinate_204_16 (Fin.cases coordinate_204_17 (Fin.cases coordinate_204_18 (Fin.cases coordinate_204_19 (Fin.cases coordinate_204_20 (Fin.cases coordinate_204_21 (Fin.cases coordinate_204_22 (Fin.cases coordinate_204_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
