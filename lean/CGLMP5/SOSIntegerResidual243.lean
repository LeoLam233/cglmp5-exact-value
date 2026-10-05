import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear00
import CGLMP5.SOSPhaseLinear07
import CGLMP5.SOSPhaseLinear10

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_243_0 : commonDenominator 243 / (gramDenominator 13 * phaseDenominator 10) = 802952008 := by
  decide +kernel

private theorem scale_243_1 : commonDenominator 243 / (gramDenominator 18 * phaseDenominator 10) = 802952008 := by
  decide +kernel

private theorem scale_243_2 : commonDenominator 243 / (gramDenominator 38 * phaseDenominator 0) = 4520539132965924886361183396826124250264393682666820928123253479273768890668091538135035060431600005327112797893962844407135314872617427843693155936770759811305229995140578282458424738123728545949745448266995035231496038287525033952680747526648610287672623360 := by
  decide +kernel

private theorem scale_243_3 : commonDenominator 243 / (gramDenominator 47 * phaseDenominator 0) = 71022490836322751700916198045014538370778772897476828733477066065204730266155102251080568492646969412072451308980662830022988767699398197572977964608388037887992035374890131082926704 := by
  decide +kernel

private theorem scale_243_4 : commonDenominator 243 / (gramDenominator 113 * phaseDenominator 7) = 445528528360835568862000598906016390421952064232851545039199273585974977330528232749612989382440760347954329843970716035452511853013104086975026431422328973947994405408398933847025089793919 := by
  decide +kernel

theorem denominator_divides_243 : ∀ f ∈ fiber 243, commonDenominator 243 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_243_0 : integerCoordinateClaim 243 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_0, phase_linear_7_0, phase_linear_10_0, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_1 : integerCoordinateClaim 243 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_1, phase_linear_7_1, phase_linear_10_1, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_2 : integerCoordinateClaim 243 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_2, phase_linear_7_2, phase_linear_10_2, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_3 : integerCoordinateClaim 243 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_3, phase_linear_7_3, phase_linear_10_3, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_4 : integerCoordinateClaim 243 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_4, phase_linear_7_4, phase_linear_10_4, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_5 : integerCoordinateClaim 243 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_5, phase_linear_7_5, phase_linear_10_5, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_6 : integerCoordinateClaim 243 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_6, phase_linear_7_6, phase_linear_10_6, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_7 : integerCoordinateClaim 243 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_7, phase_linear_7_7, phase_linear_10_7, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_8 : integerCoordinateClaim 243 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_8, phase_linear_7_8, phase_linear_10_8, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_9 : integerCoordinateClaim 243 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_9, phase_linear_7_9, phase_linear_10_9, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_10 : integerCoordinateClaim 243 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_10, phase_linear_7_10, phase_linear_10_10, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_11 : integerCoordinateClaim 243 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_11, phase_linear_7_11, phase_linear_10_11, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_12 : integerCoordinateClaim 243 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_12, phase_linear_7_12, phase_linear_10_12, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_13 : integerCoordinateClaim 243 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_13, phase_linear_7_13, phase_linear_10_13, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_14 : integerCoordinateClaim 243 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_14, phase_linear_7_14, phase_linear_10_14, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_15 : integerCoordinateClaim 243 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_15, phase_linear_7_15, phase_linear_10_15, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_16 : integerCoordinateClaim 243 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_16, phase_linear_7_16, phase_linear_10_16, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_17 : integerCoordinateClaim 243 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_17, phase_linear_7_17, phase_linear_10_17, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_18 : integerCoordinateClaim 243 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_18, phase_linear_7_18, phase_linear_10_18, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_19 : integerCoordinateClaim 243 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_19, phase_linear_7_19, phase_linear_10_19, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_20 : integerCoordinateClaim 243 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_20, phase_linear_7_20, phase_linear_10_20, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_21 : integerCoordinateClaim 243 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_21, phase_linear_7_21, phase_linear_10_21, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_22 : integerCoordinateClaim 243 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_22, phase_linear_7_22, phase_linear_10_22, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

private theorem coordinate_243_23 : integerCoordinateClaim 243 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_243]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_243_0, scale_243_1, scale_243_2, scale_243_3, scale_243_4, phase_linear_0_23, phase_linear_7_23, phase_linear_10_23, gram_numerator_literal_13, gram_numerator_literal_18, gram_numerator_literal_38, gram_numerator_literal_47, gram_numerator_literal_113, denominator_literal_243, target_denominator_literal_243, target_numerator_literal_243]
  decide +kernel

theorem integer_residual_243 : integerResidualClaim 243 :=
  (Fin.cases coordinate_243_0 (Fin.cases coordinate_243_1 (Fin.cases coordinate_243_2 (Fin.cases coordinate_243_3 (Fin.cases coordinate_243_4 (Fin.cases coordinate_243_5 (Fin.cases coordinate_243_6 (Fin.cases coordinate_243_7 (Fin.cases coordinate_243_8 (Fin.cases coordinate_243_9 (Fin.cases coordinate_243_10 (Fin.cases coordinate_243_11 (Fin.cases coordinate_243_12 (Fin.cases coordinate_243_13 (Fin.cases coordinate_243_14 (Fin.cases coordinate_243_15 (Fin.cases coordinate_243_16 (Fin.cases coordinate_243_17 (Fin.cases coordinate_243_18 (Fin.cases coordinate_243_19 (Fin.cases coordinate_243_20 (Fin.cases coordinate_243_21 (Fin.cases coordinate_243_22 (Fin.cases coordinate_243_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
