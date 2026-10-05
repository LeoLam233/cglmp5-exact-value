import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear02
import CGLMP5.SOSPhaseLinear12
import CGLMP5.SOSPhaseLinear19

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_180_0 : commonDenominator 180 / (gramDenominator 13 * phaseDenominator 2) = 100369001 := by
  decide +kernel

private theorem scale_180_1 : commonDenominator 180 / (gramDenominator 18 * phaseDenominator 2) = 100369001 := by
  decide +kernel

private theorem scale_180_2 : commonDenominator 180 / (gramDenominator 38 * phaseDenominator 12) = 565067391620740610795147924603265531283049210333352616015406684909221111333511442266879382553950000665889099736745355550891914359077178480461644492096344976413153749392572285307303092265466068243718181033374379403937004785940629244085093440831076285959077920 := by
  decide +kernel

private theorem scale_180_3 : commonDenominator 180 / (gramDenominator 47 * phaseDenominator 12) = 8877811354540343962614524755626817296347346612184603591684633258150591283269387781385071061580871176509056413622582853752873595962424774696622245576048504735999004421861266385365838 := by
  decide +kernel

private theorem scale_180_4 : commonDenominator 180 / (gramDenominator 113 * phaseDenominator 19) = 891057056721671137724001197812032780843904128465703090078398547171949954661056465499225978764881520695908659687941432070905023706026208173950052862844657947895988810816797867694050179587838 := by
  decide +kernel

theorem denominator_divides_180 : ∀ f ∈ fiber 180, commonDenominator 180 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_180_0 : integerCoordinateClaim 180 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_0, phase_linear_12_0, phase_linear_19_0, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_1 : integerCoordinateClaim 180 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_1, phase_linear_12_1, phase_linear_19_1, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_2 : integerCoordinateClaim 180 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_2, phase_linear_12_2, phase_linear_19_2, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_3 : integerCoordinateClaim 180 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_3, phase_linear_12_3, phase_linear_19_3, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_4 : integerCoordinateClaim 180 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_4, phase_linear_12_4, phase_linear_19_4, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_5 : integerCoordinateClaim 180 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_5, phase_linear_12_5, phase_linear_19_5, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_6 : integerCoordinateClaim 180 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_6, phase_linear_12_6, phase_linear_19_6, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_7 : integerCoordinateClaim 180 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_7, phase_linear_12_7, phase_linear_19_7, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_8 : integerCoordinateClaim 180 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_8, phase_linear_12_8, phase_linear_19_8, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_9 : integerCoordinateClaim 180 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_9, phase_linear_12_9, phase_linear_19_9, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_10 : integerCoordinateClaim 180 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_10, phase_linear_12_10, phase_linear_19_10, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_11 : integerCoordinateClaim 180 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_11, phase_linear_12_11, phase_linear_19_11, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_12 : integerCoordinateClaim 180 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_12, phase_linear_12_12, phase_linear_19_12, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_13 : integerCoordinateClaim 180 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_13, phase_linear_12_13, phase_linear_19_13, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_14 : integerCoordinateClaim 180 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_14, phase_linear_12_14, phase_linear_19_14, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_15 : integerCoordinateClaim 180 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_15, phase_linear_12_15, phase_linear_19_15, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_16 : integerCoordinateClaim 180 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_16, phase_linear_12_16, phase_linear_19_16, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_17 : integerCoordinateClaim 180 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_17, phase_linear_12_17, phase_linear_19_17, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_18 : integerCoordinateClaim 180 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_18, phase_linear_12_18, phase_linear_19_18, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_19 : integerCoordinateClaim 180 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_19, phase_linear_12_19, phase_linear_19_19, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_20 : integerCoordinateClaim 180 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_20, phase_linear_12_20, phase_linear_19_20, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_21 : integerCoordinateClaim 180 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_21, phase_linear_12_21, phase_linear_19_21, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_22 : integerCoordinateClaim 180 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_22, phase_linear_12_22, phase_linear_19_22, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

private theorem coordinate_180_23 : integerCoordinateClaim 180 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_180]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_180_0, scale_180_1, scale_180_2, scale_180_3, scale_180_4, phase_linear_2_23, phase_linear_12_23, phase_linear_19_23, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_180, target_denominator_literal_180, target_numerator_literal_180]
  decide +kernel

theorem integer_residual_180 : integerResidualClaim 180 :=
  (Fin.cases coordinate_180_0 (Fin.cases coordinate_180_1 (Fin.cases coordinate_180_2 (Fin.cases coordinate_180_3 (Fin.cases coordinate_180_4 (Fin.cases coordinate_180_5 (Fin.cases coordinate_180_6 (Fin.cases coordinate_180_7 (Fin.cases coordinate_180_8 (Fin.cases coordinate_180_9 (Fin.cases coordinate_180_10 (Fin.cases coordinate_180_11 (Fin.cases coordinate_180_12 (Fin.cases coordinate_180_13 (Fin.cases coordinate_180_14 (Fin.cases coordinate_180_15 (Fin.cases coordinate_180_16 (Fin.cases coordinate_180_17 (Fin.cases coordinate_180_18 (Fin.cases coordinate_180_19 (Fin.cases coordinate_180_20 (Fin.cases coordinate_180_21 (Fin.cases coordinate_180_22 (Fin.cases coordinate_180_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
