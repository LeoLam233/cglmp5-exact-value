import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear06
import CGLMP5.SOSPhaseLinear09
import CGLMP5.SOSPhaseLinear16

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_22_0 : commonDenominator 22 / (gramDenominator 7 * phaseDenominator 6) = 100369001 := by
  decide +kernel

private theorem scale_22_1 : commonDenominator 22 / (gramDenominator 22 * phaseDenominator 6) = 100369001 := by
  decide +kernel

private theorem scale_22_2 : commonDenominator 22 / (gramDenominator 32 * phaseDenominator 16) = 565067391620740610795147924603265531283049210333352616015406684909221111333511442266879382553950000665889099736745355550891914359077178480461644492096344976413153749392572285307303092265466068243718181033374379403937004785940629244085093440831076285959077920 := by
  decide +kernel

private theorem scale_22_3 : commonDenominator 22 / (gramDenominator 43 * phaseDenominator 16) = 8877811354540343962614524755626817296347346612184603591684633258150591283269387781385071061580871176509056413622582853752873595962424774696622245576048504735999004421861266385365838 := by
  decide +kernel

private theorem scale_22_4 : commonDenominator 22 / (gramDenominator 122 * phaseDenominator 9) = 445528528360835568862000598906016390421952064232851545039199273585974977330528232749612989382440760347954329843970716035452511853013104086975026431422328973947994405408398933847025089793919 := by
  decide +kernel

theorem denominator_divides_022 : ∀ f ∈ fiber 22, commonDenominator 22 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_22_0 : integerCoordinateClaim 22 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_0, phase_linear_9_0, phase_linear_16_0, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_1 : integerCoordinateClaim 22 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_1, phase_linear_9_1, phase_linear_16_1, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_2 : integerCoordinateClaim 22 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_2, phase_linear_9_2, phase_linear_16_2, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_3 : integerCoordinateClaim 22 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_3, phase_linear_9_3, phase_linear_16_3, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_4 : integerCoordinateClaim 22 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_4, phase_linear_9_4, phase_linear_16_4, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_5 : integerCoordinateClaim 22 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_5, phase_linear_9_5, phase_linear_16_5, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_6 : integerCoordinateClaim 22 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_6, phase_linear_9_6, phase_linear_16_6, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_7 : integerCoordinateClaim 22 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_7, phase_linear_9_7, phase_linear_16_7, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_8 : integerCoordinateClaim 22 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_8, phase_linear_9_8, phase_linear_16_8, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_9 : integerCoordinateClaim 22 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_9, phase_linear_9_9, phase_linear_16_9, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_10 : integerCoordinateClaim 22 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_10, phase_linear_9_10, phase_linear_16_10, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_11 : integerCoordinateClaim 22 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_11, phase_linear_9_11, phase_linear_16_11, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_12 : integerCoordinateClaim 22 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_12, phase_linear_9_12, phase_linear_16_12, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_13 : integerCoordinateClaim 22 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_13, phase_linear_9_13, phase_linear_16_13, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_14 : integerCoordinateClaim 22 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_14, phase_linear_9_14, phase_linear_16_14, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_15 : integerCoordinateClaim 22 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_15, phase_linear_9_15, phase_linear_16_15, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_16 : integerCoordinateClaim 22 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_16, phase_linear_9_16, phase_linear_16_16, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_17 : integerCoordinateClaim 22 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_17, phase_linear_9_17, phase_linear_16_17, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_18 : integerCoordinateClaim 22 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_18, phase_linear_9_18, phase_linear_16_18, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_19 : integerCoordinateClaim 22 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_19, phase_linear_9_19, phase_linear_16_19, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_20 : integerCoordinateClaim 22 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_20, phase_linear_9_20, phase_linear_16_20, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_21 : integerCoordinateClaim 22 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_21, phase_linear_9_21, phase_linear_16_21, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_22 : integerCoordinateClaim 22 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_22, phase_linear_9_22, phase_linear_16_22, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

private theorem coordinate_22_23 : integerCoordinateClaim 22 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_22]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_22_0, scale_22_1, scale_22_2, scale_22_3, scale_22_4, phase_linear_6_23, phase_linear_9_23, phase_linear_16_23, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_22, target_denominator_literal_22, target_numerator_literal_22]
  decide +kernel

theorem integer_residual_022 : integerResidualClaim 22 :=
  (Fin.cases coordinate_22_0 (Fin.cases coordinate_22_1 (Fin.cases coordinate_22_2 (Fin.cases coordinate_22_3 (Fin.cases coordinate_22_4 (Fin.cases coordinate_22_5 (Fin.cases coordinate_22_6 (Fin.cases coordinate_22_7 (Fin.cases coordinate_22_8 (Fin.cases coordinate_22_9 (Fin.cases coordinate_22_10 (Fin.cases coordinate_22_11 (Fin.cases coordinate_22_12 (Fin.cases coordinate_22_13 (Fin.cases coordinate_22_14 (Fin.cases coordinate_22_15 (Fin.cases coordinate_22_16 (Fin.cases coordinate_22_17 (Fin.cases coordinate_22_18 (Fin.cases coordinate_22_19 (Fin.cases coordinate_22_20 (Fin.cases coordinate_22_21 (Fin.cases coordinate_22_22 (Fin.cases coordinate_22_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
