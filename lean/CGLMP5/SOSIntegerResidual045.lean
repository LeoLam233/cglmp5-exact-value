import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear08
import CGLMP5.SOSPhaseLinear15
import CGLMP5.SOSPhaseLinear18

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_45_0 : commonDenominator 45 / (gramDenominator 13 * phaseDenominator 18) = 100369001 := by
  decide +kernel

private theorem scale_45_1 : commonDenominator 45 / (gramDenominator 18 * phaseDenominator 18) = 100369001 := by
  decide +kernel

private theorem scale_45_2 : commonDenominator 45 / (gramDenominator 38 * phaseDenominator 8) = 565067391620740610795147924603265531283049210333352616015406684909221111333511442266879382553950000665889099736745355550891914359077178480461644492096344976413153749392572285307303092265466068243718181033374379403937004785940629244085093440831076285959077920 := by
  decide +kernel

private theorem scale_45_3 : commonDenominator 45 / (gramDenominator 47 * phaseDenominator 8) = 8877811354540343962614524755626817296347346612184603591684633258150591283269387781385071061580871176509056413622582853752873595962424774696622245576048504735999004421861266385365838 := by
  decide +kernel

private theorem scale_45_4 : commonDenominator 45 / (gramDenominator 113 * phaseDenominator 15) = 3564228226886684550896004791248131123375616513862812360313594188687799818644225861996903915059526082783634638751765728283620094824104832695800211451378631791583955243267191470776200718351352 := by
  decide +kernel

theorem denominator_divides_045 : ∀ f ∈ fiber 45, commonDenominator 45 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_45_0 : integerCoordinateClaim 45 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_0, phase_linear_15_0, phase_linear_18_0, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_1 : integerCoordinateClaim 45 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_1, phase_linear_15_1, phase_linear_18_1, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_2 : integerCoordinateClaim 45 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_2, phase_linear_15_2, phase_linear_18_2, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_3 : integerCoordinateClaim 45 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_3, phase_linear_15_3, phase_linear_18_3, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_4 : integerCoordinateClaim 45 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_4, phase_linear_15_4, phase_linear_18_4, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_5 : integerCoordinateClaim 45 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_5, phase_linear_15_5, phase_linear_18_5, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_6 : integerCoordinateClaim 45 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_6, phase_linear_15_6, phase_linear_18_6, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_7 : integerCoordinateClaim 45 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_7, phase_linear_15_7, phase_linear_18_7, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_8 : integerCoordinateClaim 45 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_8, phase_linear_15_8, phase_linear_18_8, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_9 : integerCoordinateClaim 45 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_9, phase_linear_15_9, phase_linear_18_9, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_10 : integerCoordinateClaim 45 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_10, phase_linear_15_10, phase_linear_18_10, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_11 : integerCoordinateClaim 45 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_11, phase_linear_15_11, phase_linear_18_11, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_12 : integerCoordinateClaim 45 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_12, phase_linear_15_12, phase_linear_18_12, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_13 : integerCoordinateClaim 45 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_13, phase_linear_15_13, phase_linear_18_13, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_14 : integerCoordinateClaim 45 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_14, phase_linear_15_14, phase_linear_18_14, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_15 : integerCoordinateClaim 45 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_15, phase_linear_15_15, phase_linear_18_15, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_16 : integerCoordinateClaim 45 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_16, phase_linear_15_16, phase_linear_18_16, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_17 : integerCoordinateClaim 45 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_17, phase_linear_15_17, phase_linear_18_17, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_18 : integerCoordinateClaim 45 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_18, phase_linear_15_18, phase_linear_18_18, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_19 : integerCoordinateClaim 45 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_19, phase_linear_15_19, phase_linear_18_19, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_20 : integerCoordinateClaim 45 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_20, phase_linear_15_20, phase_linear_18_20, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_21 : integerCoordinateClaim 45 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_21, phase_linear_15_21, phase_linear_18_21, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_22 : integerCoordinateClaim 45 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_22, phase_linear_15_22, phase_linear_18_22, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

private theorem coordinate_45_23 : integerCoordinateClaim 45 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_45]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_45_0, scale_45_1, scale_45_2, scale_45_3, scale_45_4, phase_linear_8_23, phase_linear_15_23, phase_linear_18_23, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_45, target_denominator_literal_45, target_numerator_literal_45]
  decide +kernel

theorem integer_residual_045 : integerResidualClaim 45 :=
  (Fin.cases coordinate_45_0 (Fin.cases coordinate_45_1 (Fin.cases coordinate_45_2 (Fin.cases coordinate_45_3 (Fin.cases coordinate_45_4 (Fin.cases coordinate_45_5 (Fin.cases coordinate_45_6 (Fin.cases coordinate_45_7 (Fin.cases coordinate_45_8 (Fin.cases coordinate_45_9 (Fin.cases coordinate_45_10 (Fin.cases coordinate_45_11 (Fin.cases coordinate_45_12 (Fin.cases coordinate_45_13 (Fin.cases coordinate_45_14 (Fin.cases coordinate_45_15 (Fin.cases coordinate_45_16 (Fin.cases coordinate_45_17 (Fin.cases coordinate_45_18 (Fin.cases coordinate_45_19 (Fin.cases coordinate_45_20 (Fin.cases coordinate_45_21 (Fin.cases coordinate_45_22 (Fin.cases coordinate_45_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
