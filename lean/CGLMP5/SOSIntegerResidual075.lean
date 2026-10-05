import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear00
import CGLMP5.SOSPhaseLinear10
import CGLMP5.SOSPhaseLinear13

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_75_0 : commonDenominator 75 / (gramDenominator 7 * phaseDenominator 10) = 802952008 := by
  decide +kernel

private theorem scale_75_1 : commonDenominator 75 / (gramDenominator 22 * phaseDenominator 10) = 802952008 := by
  decide +kernel

private theorem scale_75_2 : commonDenominator 75 / (gramDenominator 32 * phaseDenominator 0) = 4520539132965924886361183396826124250264393682666820928123253479273768890668091538135035060431600005327112797893962844407135314872617427843693155936770759811305229995140578282458424738123728545949745448266995035231496038287525033952680747526648610287672623360 := by
  decide +kernel

private theorem scale_75_3 : commonDenominator 75 / (gramDenominator 43 * phaseDenominator 0) = 71022490836322751700916198045014538370778772897476828733477066065204730266155102251080568492646969412072451308980662830022988767699398197572977964608388037887992035374890131082926704 := by
  decide +kernel

private theorem scale_75_4 : commonDenominator 75 / (gramDenominator 122 * phaseDenominator 13) = 445528528360835568862000598906016390421952064232851545039199273585974977330528232749612989382440760347954329843970716035452511853013104086975026431422328973947994405408398933847025089793919 := by
  decide +kernel

theorem denominator_divides_075 : ∀ f ∈ fiber 75, commonDenominator 75 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_75_0 : integerCoordinateClaim 75 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_0, phase_linear_10_0, phase_linear_13_0, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_1 : integerCoordinateClaim 75 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_1, phase_linear_10_1, phase_linear_13_1, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_2 : integerCoordinateClaim 75 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_2, phase_linear_10_2, phase_linear_13_2, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_3 : integerCoordinateClaim 75 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_3, phase_linear_10_3, phase_linear_13_3, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_4 : integerCoordinateClaim 75 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_4, phase_linear_10_4, phase_linear_13_4, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_5 : integerCoordinateClaim 75 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_5, phase_linear_10_5, phase_linear_13_5, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_6 : integerCoordinateClaim 75 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_6, phase_linear_10_6, phase_linear_13_6, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_7 : integerCoordinateClaim 75 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_7, phase_linear_10_7, phase_linear_13_7, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_8 : integerCoordinateClaim 75 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_8, phase_linear_10_8, phase_linear_13_8, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_9 : integerCoordinateClaim 75 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_9, phase_linear_10_9, phase_linear_13_9, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_10 : integerCoordinateClaim 75 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_10, phase_linear_10_10, phase_linear_13_10, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_11 : integerCoordinateClaim 75 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_11, phase_linear_10_11, phase_linear_13_11, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_12 : integerCoordinateClaim 75 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_12, phase_linear_10_12, phase_linear_13_12, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_13 : integerCoordinateClaim 75 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_13, phase_linear_10_13, phase_linear_13_13, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_14 : integerCoordinateClaim 75 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_14, phase_linear_10_14, phase_linear_13_14, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_15 : integerCoordinateClaim 75 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_15, phase_linear_10_15, phase_linear_13_15, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_16 : integerCoordinateClaim 75 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_16, phase_linear_10_16, phase_linear_13_16, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_17 : integerCoordinateClaim 75 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_17, phase_linear_10_17, phase_linear_13_17, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_18 : integerCoordinateClaim 75 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_18, phase_linear_10_18, phase_linear_13_18, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_19 : integerCoordinateClaim 75 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_19, phase_linear_10_19, phase_linear_13_19, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_20 : integerCoordinateClaim 75 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_20, phase_linear_10_20, phase_linear_13_20, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_21 : integerCoordinateClaim 75 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_21, phase_linear_10_21, phase_linear_13_21, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_22 : integerCoordinateClaim 75 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_22, phase_linear_10_22, phase_linear_13_22, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

private theorem coordinate_75_23 : integerCoordinateClaim 75 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_75]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_75_0, scale_75_1, scale_75_2, scale_75_3, scale_75_4, phase_linear_0_23, phase_linear_10_23, phase_linear_13_23, gram_numerator_literal_7, gram_numerator_literal_22, gram_numerator_literal_32, gram_numerator_literal_43, gram_numerator_literal_122, denominator_literal_75, target_denominator_literal_75, target_numerator_literal_75]
  decide +kernel

theorem integer_residual_075 : integerResidualClaim 75 :=
  (Fin.cases coordinate_75_0 (Fin.cases coordinate_75_1 (Fin.cases coordinate_75_2 (Fin.cases coordinate_75_3 (Fin.cases coordinate_75_4 (Fin.cases coordinate_75_5 (Fin.cases coordinate_75_6 (Fin.cases coordinate_75_7 (Fin.cases coordinate_75_8 (Fin.cases coordinate_75_9 (Fin.cases coordinate_75_10 (Fin.cases coordinate_75_11 (Fin.cases coordinate_75_12 (Fin.cases coordinate_75_13 (Fin.cases coordinate_75_14 (Fin.cases coordinate_75_15 (Fin.cases coordinate_75_16 (Fin.cases coordinate_75_17 (Fin.cases coordinate_75_18 (Fin.cases coordinate_75_19 (Fin.cases coordinate_75_20 (Fin.cases coordinate_75_21 (Fin.cases coordinate_75_22 (Fin.cases coordinate_75_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
