import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear04
import CGLMP5.SOSPhaseLinear14

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_158_0 : commonDenominator 158 / (gramDenominator 5 * phaseDenominator 14) = 100369001 := by
  decide +kernel

private theorem scale_158_1 : commonDenominator 158 / (gramDenominator 24 * phaseDenominator 14) = 100369001 := by
  decide +kernel

private theorem scale_158_2 : commonDenominator 158 / (gramDenominator 30 * phaseDenominator 4) = 282533695810370305397573962301632765641524605166676308007703342454610555666755721133439691276975000332944549868372677775445957179538589240230822246048172488206576874696286142653651546132733034121859090516687189701968502392970314622042546720415538142979538960 := by
  decide +kernel

private theorem scale_158_3 : commonDenominator 158 / (gramDenominator 41 * phaseDenominator 4) = 17755622709080687925229049511253634592694693224369207183369266516301182566538775562770142123161742353018112827245165707505747191924849549393244491152097009471998008843722532770731676 := by
  decide +kernel

private theorem scale_158_4 : commonDenominator 158 / (gramDenominator 110 * phaseDenominator 14) = 445528528360835568862000598906016390421952064232851545039199273585974977330528232749612989382440760347954329843970716035452511853013104086975026431422328973947994405408398933847025089793919 := by
  decide +kernel

theorem denominator_divides_158 : ∀ f ∈ fiber 158, commonDenominator 158 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_158_0 : integerCoordinateClaim 158 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_0, phase_linear_14_0, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_1 : integerCoordinateClaim 158 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_1, phase_linear_14_1, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_2 : integerCoordinateClaim 158 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_2, phase_linear_14_2, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_3 : integerCoordinateClaim 158 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_3, phase_linear_14_3, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_4 : integerCoordinateClaim 158 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_4, phase_linear_14_4, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_5 : integerCoordinateClaim 158 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_5, phase_linear_14_5, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_6 : integerCoordinateClaim 158 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_6, phase_linear_14_6, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_7 : integerCoordinateClaim 158 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_7, phase_linear_14_7, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_8 : integerCoordinateClaim 158 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_8, phase_linear_14_8, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_9 : integerCoordinateClaim 158 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_9, phase_linear_14_9, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_10 : integerCoordinateClaim 158 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_10, phase_linear_14_10, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_11 : integerCoordinateClaim 158 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_11, phase_linear_14_11, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_12 : integerCoordinateClaim 158 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_12, phase_linear_14_12, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_13 : integerCoordinateClaim 158 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_13, phase_linear_14_13, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_14 : integerCoordinateClaim 158 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_14, phase_linear_14_14, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_15 : integerCoordinateClaim 158 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_15, phase_linear_14_15, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_16 : integerCoordinateClaim 158 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_16, phase_linear_14_16, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_17 : integerCoordinateClaim 158 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_17, phase_linear_14_17, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_18 : integerCoordinateClaim 158 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_18, phase_linear_14_18, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_19 : integerCoordinateClaim 158 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_19, phase_linear_14_19, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_20 : integerCoordinateClaim 158 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_20, phase_linear_14_20, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_21 : integerCoordinateClaim 158 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_21, phase_linear_14_21, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_22 : integerCoordinateClaim 158 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_22, phase_linear_14_22, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

private theorem coordinate_158_23 : integerCoordinateClaim 158 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_158]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_158_0, scale_158_1, scale_158_2, scale_158_3, scale_158_4, phase_linear_4_23, phase_linear_14_23, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_158, target_denominator_literal_158, target_numerator_literal_158]
  decide +kernel

theorem integer_residual_158 : integerResidualClaim 158 :=
  (Fin.cases coordinate_158_0 (Fin.cases coordinate_158_1 (Fin.cases coordinate_158_2 (Fin.cases coordinate_158_3 (Fin.cases coordinate_158_4 (Fin.cases coordinate_158_5 (Fin.cases coordinate_158_6 (Fin.cases coordinate_158_7 (Fin.cases coordinate_158_8 (Fin.cases coordinate_158_9 (Fin.cases coordinate_158_10 (Fin.cases coordinate_158_11 (Fin.cases coordinate_158_12 (Fin.cases coordinate_158_13 (Fin.cases coordinate_158_14 (Fin.cases coordinate_158_15 (Fin.cases coordinate_158_16 (Fin.cases coordinate_158_17 (Fin.cases coordinate_158_18 (Fin.cases coordinate_158_19 (Fin.cases coordinate_158_20 (Fin.cases coordinate_158_21 (Fin.cases coordinate_158_22 (Fin.cases coordinate_158_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
