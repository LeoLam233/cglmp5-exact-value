import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear02
import CGLMP5.SOSPhaseLinear05
import CGLMP5.SOSPhaseLinear12

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_219_0 : commonDenominator 219 / (gramDenominator 7 * phaseDenominator 2) = 100369001 := by
  decide +kernel

private theorem scale_219_1 : commonDenominator 219 / (gramDenominator 22 * phaseDenominator 2) = 100369001 := by
  decide +kernel

private theorem scale_219_2 : commonDenominator 219 / (gramDenominator 32 * phaseDenominator 12) = 565067391620740610795147924603265531283049210333352616015406684909221111333511442266879382553950000665889099736745355550891914359077178480461644492096344976413153749392572285307303092265466068243718181033374379403937004785940629244085093440831076285959077920 := by
  decide +kernel

private theorem scale_219_3 : commonDenominator 219 / (gramDenominator 43 * phaseDenominator 12) = 8877811354540343962614524755626817296347346612184603591684633258150591283269387781385071061580871176509056413622582853752873595962424774696622245576048504735999004421861266385365838 := by
  decide +kernel

private theorem scale_219_4 : commonDenominator 219 / (gramDenominator 122 * phaseDenominator 5) = 3564228226886684550896004791248131123375616513862812360313594188687799818644225861996903915059526082783634638751765728283620094824104832695800211451378631791583955243267191470776200718351352 := by
  decide +kernel

theorem denominator_divides_219 : ∀ f ∈ fiber 219, commonDenominator 219 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_219_0 : integerCoordinateClaim 219 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_0, phase_linear_5_0, phase_linear_12_0, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_1 : integerCoordinateClaim 219 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_1, phase_linear_5_1, phase_linear_12_1, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_2 : integerCoordinateClaim 219 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_2, phase_linear_5_2, phase_linear_12_2, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_3 : integerCoordinateClaim 219 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_3, phase_linear_5_3, phase_linear_12_3, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_4 : integerCoordinateClaim 219 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_4, phase_linear_5_4, phase_linear_12_4, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_5 : integerCoordinateClaim 219 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_5, phase_linear_5_5, phase_linear_12_5, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_6 : integerCoordinateClaim 219 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_6, phase_linear_5_6, phase_linear_12_6, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_7 : integerCoordinateClaim 219 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_7, phase_linear_5_7, phase_linear_12_7, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_8 : integerCoordinateClaim 219 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_8, phase_linear_5_8, phase_linear_12_8, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_9 : integerCoordinateClaim 219 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_9, phase_linear_5_9, phase_linear_12_9, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_10 : integerCoordinateClaim 219 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_10, phase_linear_5_10, phase_linear_12_10, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_11 : integerCoordinateClaim 219 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_11, phase_linear_5_11, phase_linear_12_11, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_12 : integerCoordinateClaim 219 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_12, phase_linear_5_12, phase_linear_12_12, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_13 : integerCoordinateClaim 219 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_13, phase_linear_5_13, phase_linear_12_13, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_14 : integerCoordinateClaim 219 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_14, phase_linear_5_14, phase_linear_12_14, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_15 : integerCoordinateClaim 219 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_15, phase_linear_5_15, phase_linear_12_15, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_16 : integerCoordinateClaim 219 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_16, phase_linear_5_16, phase_linear_12_16, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_17 : integerCoordinateClaim 219 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_17, phase_linear_5_17, phase_linear_12_17, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_18 : integerCoordinateClaim 219 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_18, phase_linear_5_18, phase_linear_12_18, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_19 : integerCoordinateClaim 219 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_19, phase_linear_5_19, phase_linear_12_19, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_20 : integerCoordinateClaim 219 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_20, phase_linear_5_20, phase_linear_12_20, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_21 : integerCoordinateClaim 219 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_21, phase_linear_5_21, phase_linear_12_21, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_22 : integerCoordinateClaim 219 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_22, phase_linear_5_22, phase_linear_12_22, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

private theorem coordinate_219_23 : integerCoordinateClaim 219 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_219]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_219_0, scale_219_1, scale_219_2, scale_219_3, scale_219_4, phase_linear_2_23, phase_linear_5_23, phase_linear_12_23, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_219, target_denominator_literal_219, target_numerator_literal_219]
  decide +kernel

theorem integer_residual_219 : integerResidualClaim 219 :=
  (Fin.cases coordinate_219_0 (Fin.cases coordinate_219_1 (Fin.cases coordinate_219_2 (Fin.cases coordinate_219_3 (Fin.cases coordinate_219_4 (Fin.cases coordinate_219_5 (Fin.cases coordinate_219_6 (Fin.cases coordinate_219_7 (Fin.cases coordinate_219_8 (Fin.cases coordinate_219_9 (Fin.cases coordinate_219_10 (Fin.cases coordinate_219_11 (Fin.cases coordinate_219_12 (Fin.cases coordinate_219_13 (Fin.cases coordinate_219_14 (Fin.cases coordinate_219_15 (Fin.cases coordinate_219_16 (Fin.cases coordinate_219_17 (Fin.cases coordinate_219_18 (Fin.cases coordinate_219_19 (Fin.cases coordinate_219_20 (Fin.cases coordinate_219_21 (Fin.cases coordinate_219_22 (Fin.cases coordinate_219_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
