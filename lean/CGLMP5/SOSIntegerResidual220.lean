import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear01
import CGLMP5.SOSPhaseLinear08
import CGLMP5.SOSPhaseLinear18

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_220_0 : commonDenominator 220 / (gramDenominator 7 * phaseDenominator 18) = 100369001 := by
  decide +kernel

private theorem scale_220_1 : commonDenominator 220 / (gramDenominator 22 * phaseDenominator 18) = 100369001 := by
  decide +kernel

private theorem scale_220_2 : commonDenominator 220 / (gramDenominator 32 * phaseDenominator 8) = 565067391620740610795147924603265531283049210333352616015406684909221111333511442266879382553950000665889099736745355550891914359077178480461644492096344976413153749392572285307303092265466068243718181033374379403937004785940629244085093440831076285959077920 := by
  decide +kernel

private theorem scale_220_3 : commonDenominator 220 / (gramDenominator 43 * phaseDenominator 8) = 8877811354540343962614524755626817296347346612184603591684633258150591283269387781385071061580871176509056413622582853752873595962424774696622245576048504735999004421861266385365838 := by
  decide +kernel

private theorem scale_220_4 : commonDenominator 220 / (gramDenominator 122 * phaseDenominator 1) = 891057056721671137724001197812032780843904128465703090078398547171949954661056465499225978764881520695908659687941432070905023706026208173950052862844657947895988810816797867694050179587838 := by
  decide +kernel

theorem denominator_divides_220 : ∀ f ∈ fiber 220, commonDenominator 220 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_220_0 : integerCoordinateClaim 220 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_0, phase_linear_8_0, phase_linear_18_0, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_1 : integerCoordinateClaim 220 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_1, phase_linear_8_1, phase_linear_18_1, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_2 : integerCoordinateClaim 220 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_2, phase_linear_8_2, phase_linear_18_2, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_3 : integerCoordinateClaim 220 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_3, phase_linear_8_3, phase_linear_18_3, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_4 : integerCoordinateClaim 220 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_4, phase_linear_8_4, phase_linear_18_4, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_5 : integerCoordinateClaim 220 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_5, phase_linear_8_5, phase_linear_18_5, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_6 : integerCoordinateClaim 220 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_6, phase_linear_8_6, phase_linear_18_6, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_7 : integerCoordinateClaim 220 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_7, phase_linear_8_7, phase_linear_18_7, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_8 : integerCoordinateClaim 220 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_8, phase_linear_8_8, phase_linear_18_8, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_9 : integerCoordinateClaim 220 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_9, phase_linear_8_9, phase_linear_18_9, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_10 : integerCoordinateClaim 220 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_10, phase_linear_8_10, phase_linear_18_10, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_11 : integerCoordinateClaim 220 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_11, phase_linear_8_11, phase_linear_18_11, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_12 : integerCoordinateClaim 220 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_12, phase_linear_8_12, phase_linear_18_12, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_13 : integerCoordinateClaim 220 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_13, phase_linear_8_13, phase_linear_18_13, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_14 : integerCoordinateClaim 220 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_14, phase_linear_8_14, phase_linear_18_14, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_15 : integerCoordinateClaim 220 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_15, phase_linear_8_15, phase_linear_18_15, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_16 : integerCoordinateClaim 220 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_16, phase_linear_8_16, phase_linear_18_16, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_17 : integerCoordinateClaim 220 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_17, phase_linear_8_17, phase_linear_18_17, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_18 : integerCoordinateClaim 220 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_18, phase_linear_8_18, phase_linear_18_18, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_19 : integerCoordinateClaim 220 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_19, phase_linear_8_19, phase_linear_18_19, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_20 : integerCoordinateClaim 220 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_20, phase_linear_8_20, phase_linear_18_20, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_21 : integerCoordinateClaim 220 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_21, phase_linear_8_21, phase_linear_18_21, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_22 : integerCoordinateClaim 220 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_22, phase_linear_8_22, phase_linear_18_22, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

private theorem coordinate_220_23 : integerCoordinateClaim 220 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_220]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_220_0, scale_220_1, scale_220_2, scale_220_3, scale_220_4, phase_linear_1_23, phase_linear_8_23, phase_linear_18_23, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_220, target_denominator_literal_220, target_numerator_literal_220]
  decide +kernel

theorem integer_residual_220 : integerResidualClaim 220 :=
  (Fin.cases coordinate_220_0 (Fin.cases coordinate_220_1 (Fin.cases coordinate_220_2 (Fin.cases coordinate_220_3 (Fin.cases coordinate_220_4 (Fin.cases coordinate_220_5 (Fin.cases coordinate_220_6 (Fin.cases coordinate_220_7 (Fin.cases coordinate_220_8 (Fin.cases coordinate_220_9 (Fin.cases coordinate_220_10 (Fin.cases coordinate_220_11 (Fin.cases coordinate_220_12 (Fin.cases coordinate_220_13 (Fin.cases coordinate_220_14 (Fin.cases coordinate_220_15 (Fin.cases coordinate_220_16 (Fin.cases coordinate_220_17 (Fin.cases coordinate_220_18 (Fin.cases coordinate_220_19 (Fin.cases coordinate_220_20 (Fin.cases coordinate_220_21 (Fin.cases coordinate_220_22 (Fin.cases coordinate_220_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
