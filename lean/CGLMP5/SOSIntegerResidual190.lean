import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear04
import CGLMP5.SOSPhaseLinear11
import CGLMP5.SOSPhaseLinear14

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_190_0 : commonDenominator 190 / (gramDenominator 13 * phaseDenominator 14) = 100369001 := by
  decide +kernel

private theorem scale_190_1 : commonDenominator 190 / (gramDenominator 18 * phaseDenominator 14) = 100369001 := by
  decide +kernel

private theorem scale_190_2 : commonDenominator 190 / (gramDenominator 38 * phaseDenominator 4) = 565067391620740610795147924603265531283049210333352616015406684909221111333511442266879382553950000665889099736745355550891914359077178480461644492096344976413153749392572285307303092265466068243718181033374379403937004785940629244085093440831076285959077920 := by
  decide +kernel

private theorem scale_190_3 : commonDenominator 190 / (gramDenominator 47 * phaseDenominator 4) = 8877811354540343962614524755626817296347346612184603591684633258150591283269387781385071061580871176509056413622582853752873595962424774696622245576048504735999004421861266385365838 := by
  decide +kernel

private theorem scale_190_4 : commonDenominator 190 / (gramDenominator 113 * phaseDenominator 11) = 445528528360835568862000598906016390421952064232851545039199273585974977330528232749612989382440760347954329843970716035452511853013104086975026431422328973947994405408398933847025089793919 := by
  decide +kernel

theorem denominator_divides_190 : ∀ f ∈ fiber 190, commonDenominator 190 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_190_0 : integerCoordinateClaim 190 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_0, phase_linear_11_0, phase_linear_14_0, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_1 : integerCoordinateClaim 190 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_1, phase_linear_11_1, phase_linear_14_1, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_2 : integerCoordinateClaim 190 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_2, phase_linear_11_2, phase_linear_14_2, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_3 : integerCoordinateClaim 190 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_3, phase_linear_11_3, phase_linear_14_3, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_4 : integerCoordinateClaim 190 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_4, phase_linear_11_4, phase_linear_14_4, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_5 : integerCoordinateClaim 190 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_5, phase_linear_11_5, phase_linear_14_5, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_6 : integerCoordinateClaim 190 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_6, phase_linear_11_6, phase_linear_14_6, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_7 : integerCoordinateClaim 190 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_7, phase_linear_11_7, phase_linear_14_7, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_8 : integerCoordinateClaim 190 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_8, phase_linear_11_8, phase_linear_14_8, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_9 : integerCoordinateClaim 190 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_9, phase_linear_11_9, phase_linear_14_9, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_10 : integerCoordinateClaim 190 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_10, phase_linear_11_10, phase_linear_14_10, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_11 : integerCoordinateClaim 190 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_11, phase_linear_11_11, phase_linear_14_11, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_12 : integerCoordinateClaim 190 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_12, phase_linear_11_12, phase_linear_14_12, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_13 : integerCoordinateClaim 190 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_13, phase_linear_11_13, phase_linear_14_13, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_14 : integerCoordinateClaim 190 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_14, phase_linear_11_14, phase_linear_14_14, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_15 : integerCoordinateClaim 190 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_15, phase_linear_11_15, phase_linear_14_15, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_16 : integerCoordinateClaim 190 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_16, phase_linear_11_16, phase_linear_14_16, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_17 : integerCoordinateClaim 190 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_17, phase_linear_11_17, phase_linear_14_17, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_18 : integerCoordinateClaim 190 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_18, phase_linear_11_18, phase_linear_14_18, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_19 : integerCoordinateClaim 190 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_19, phase_linear_11_19, phase_linear_14_19, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_20 : integerCoordinateClaim 190 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_20, phase_linear_11_20, phase_linear_14_20, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_21 : integerCoordinateClaim 190 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_21, phase_linear_11_21, phase_linear_14_21, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_22 : integerCoordinateClaim 190 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_22, phase_linear_11_22, phase_linear_14_22, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

private theorem coordinate_190_23 : integerCoordinateClaim 190 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_190]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_190_0, scale_190_1, scale_190_2, scale_190_3, scale_190_4, phase_linear_4_23, phase_linear_11_23, phase_linear_14_23, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_190, target_denominator_literal_190, target_numerator_literal_190]
  decide +kernel

theorem integer_residual_190 : integerResidualClaim 190 :=
  (Fin.cases coordinate_190_0 (Fin.cases coordinate_190_1 (Fin.cases coordinate_190_2 (Fin.cases coordinate_190_3 (Fin.cases coordinate_190_4 (Fin.cases coordinate_190_5 (Fin.cases coordinate_190_6 (Fin.cases coordinate_190_7 (Fin.cases coordinate_190_8 (Fin.cases coordinate_190_9 (Fin.cases coordinate_190_10 (Fin.cases coordinate_190_11 (Fin.cases coordinate_190_12 (Fin.cases coordinate_190_13 (Fin.cases coordinate_190_14 (Fin.cases coordinate_190_15 (Fin.cases coordinate_190_16 (Fin.cases coordinate_190_17 (Fin.cases coordinate_190_18 (Fin.cases coordinate_190_19 (Fin.cases coordinate_190_20 (Fin.cases coordinate_190_21 (Fin.cases coordinate_190_22 (Fin.cases coordinate_190_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
