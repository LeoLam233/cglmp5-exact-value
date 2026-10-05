import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear04
import CGLMP5.SOSPhaseLinear11
import CGLMP5.SOSPhaseLinear14

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_114_0 : commonDenominator 114 / (gramDenominator 13 * phaseDenominator 14) = 100369001 := by
  decide +kernel

private theorem scale_114_1 : commonDenominator 114 / (gramDenominator 18 * phaseDenominator 14) = 100369001 := by
  decide +kernel

private theorem scale_114_2 : commonDenominator 114 / (gramDenominator 38 * phaseDenominator 4) = 565067391620740610795147924603265531283049210333352616015406684909221111333511442266879382553950000665889099736745355550891914359077178480461644492096344976413153749392572285307303092265466068243718181033374379403937004785940629244085093440831076285959077920 := by
  decide +kernel

private theorem scale_114_3 : commonDenominator 114 / (gramDenominator 47 * phaseDenominator 4) = 8877811354540343962614524755626817296347346612184603591684633258150591283269387781385071061580871176509056413622582853752873595962424774696622245576048504735999004421861266385365838 := by
  decide +kernel

private theorem scale_114_4 : commonDenominator 114 / (gramDenominator 113 * phaseDenominator 11) = 445528528360835568862000598906016390421952064232851545039199273585974977330528232749612989382440760347954329843970716035452511853013104086975026431422328973947994405408398933847025089793919 := by
  decide +kernel

theorem denominator_divides_114 : ∀ f ∈ fiber 114, commonDenominator 114 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_114_0 : integerCoordinateClaim 114 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_0, phase_linear_11_0, phase_linear_14_0, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_1 : integerCoordinateClaim 114 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_1, phase_linear_11_1, phase_linear_14_1, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_2 : integerCoordinateClaim 114 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_2, phase_linear_11_2, phase_linear_14_2, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_3 : integerCoordinateClaim 114 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_3, phase_linear_11_3, phase_linear_14_3, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_4 : integerCoordinateClaim 114 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_4, phase_linear_11_4, phase_linear_14_4, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_5 : integerCoordinateClaim 114 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_5, phase_linear_11_5, phase_linear_14_5, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_6 : integerCoordinateClaim 114 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_6, phase_linear_11_6, phase_linear_14_6, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_7 : integerCoordinateClaim 114 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_7, phase_linear_11_7, phase_linear_14_7, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_8 : integerCoordinateClaim 114 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_8, phase_linear_11_8, phase_linear_14_8, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_9 : integerCoordinateClaim 114 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_9, phase_linear_11_9, phase_linear_14_9, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_10 : integerCoordinateClaim 114 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_10, phase_linear_11_10, phase_linear_14_10, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_11 : integerCoordinateClaim 114 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_11, phase_linear_11_11, phase_linear_14_11, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_12 : integerCoordinateClaim 114 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_12, phase_linear_11_12, phase_linear_14_12, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_13 : integerCoordinateClaim 114 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_13, phase_linear_11_13, phase_linear_14_13, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_14 : integerCoordinateClaim 114 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_14, phase_linear_11_14, phase_linear_14_14, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_15 : integerCoordinateClaim 114 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_15, phase_linear_11_15, phase_linear_14_15, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_16 : integerCoordinateClaim 114 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_16, phase_linear_11_16, phase_linear_14_16, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_17 : integerCoordinateClaim 114 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_17, phase_linear_11_17, phase_linear_14_17, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_18 : integerCoordinateClaim 114 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_18, phase_linear_11_18, phase_linear_14_18, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_19 : integerCoordinateClaim 114 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_19, phase_linear_11_19, phase_linear_14_19, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_20 : integerCoordinateClaim 114 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_20, phase_linear_11_20, phase_linear_14_20, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_21 : integerCoordinateClaim 114 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_21, phase_linear_11_21, phase_linear_14_21, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_22 : integerCoordinateClaim 114 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_22, phase_linear_11_22, phase_linear_14_22, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

private theorem coordinate_114_23 : integerCoordinateClaim 114 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_114]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_114_0, scale_114_1, scale_114_2, scale_114_3, scale_114_4, phase_linear_4_23, phase_linear_11_23, phase_linear_14_23, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_114, target_denominator_literal_114, target_numerator_literal_114]
  decide +kernel

theorem integer_residual_114 : integerResidualClaim 114 :=
  (Fin.cases coordinate_114_0 (Fin.cases coordinate_114_1 (Fin.cases coordinate_114_2 (Fin.cases coordinate_114_3 (Fin.cases coordinate_114_4 (Fin.cases coordinate_114_5 (Fin.cases coordinate_114_6 (Fin.cases coordinate_114_7 (Fin.cases coordinate_114_8 (Fin.cases coordinate_114_9 (Fin.cases coordinate_114_10 (Fin.cases coordinate_114_11 (Fin.cases coordinate_114_12 (Fin.cases coordinate_114_13 (Fin.cases coordinate_114_14 (Fin.cases coordinate_114_15 (Fin.cases coordinate_114_16 (Fin.cases coordinate_114_17 (Fin.cases coordinate_114_18 (Fin.cases coordinate_114_19 (Fin.cases coordinate_114_20 (Fin.cases coordinate_114_21 (Fin.cases coordinate_114_22 (Fin.cases coordinate_114_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
