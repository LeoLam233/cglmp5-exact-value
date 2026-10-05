import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear06
import CGLMP5.SOSPhaseLinear16

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_29_0 : commonDenominator 29 / (gramDenominator 5 * phaseDenominator 6) = 100369001 := by
  decide +kernel

private theorem scale_29_1 : commonDenominator 29 / (gramDenominator 24 * phaseDenominator 6) = 100369001 := by
  decide +kernel

private theorem scale_29_2 : commonDenominator 29 / (gramDenominator 30 * phaseDenominator 16) = 282533695810370305397573962301632765641524605166676308007703342454610555666755721133439691276975000332944549868372677775445957179538589240230822246048172488206576874696286142653651546132733034121859090516687189701968502392970314622042546720415538142979538960 := by
  decide +kernel

private theorem scale_29_3 : commonDenominator 29 / (gramDenominator 41 * phaseDenominator 16) = 17755622709080687925229049511253634592694693224369207183369266516301182566538775562770142123161742353018112827245165707505747191924849549393244491152097009471998008843722532770731676 := by
  decide +kernel

private theorem scale_29_4 : commonDenominator 29 / (gramDenominator 110 * phaseDenominator 6) = 445528528360835568862000598906016390421952064232851545039199273585974977330528232749612989382440760347954329843970716035452511853013104086975026431422328973947994405408398933847025089793919 := by
  decide +kernel

theorem denominator_divides_029 : ∀ f ∈ fiber 29, commonDenominator 29 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_29_0 : integerCoordinateClaim 29 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_0, phase_linear_16_0, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_1 : integerCoordinateClaim 29 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_1, phase_linear_16_1, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_2 : integerCoordinateClaim 29 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_2, phase_linear_16_2, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_3 : integerCoordinateClaim 29 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_3, phase_linear_16_3, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_4 : integerCoordinateClaim 29 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_4, phase_linear_16_4, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_5 : integerCoordinateClaim 29 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_5, phase_linear_16_5, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_6 : integerCoordinateClaim 29 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_6, phase_linear_16_6, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_7 : integerCoordinateClaim 29 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_7, phase_linear_16_7, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_8 : integerCoordinateClaim 29 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_8, phase_linear_16_8, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_9 : integerCoordinateClaim 29 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_9, phase_linear_16_9, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_10 : integerCoordinateClaim 29 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_10, phase_linear_16_10, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_11 : integerCoordinateClaim 29 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_11, phase_linear_16_11, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_12 : integerCoordinateClaim 29 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_12, phase_linear_16_12, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_13 : integerCoordinateClaim 29 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_13, phase_linear_16_13, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_14 : integerCoordinateClaim 29 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_14, phase_linear_16_14, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_15 : integerCoordinateClaim 29 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_15, phase_linear_16_15, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_16 : integerCoordinateClaim 29 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_16, phase_linear_16_16, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_17 : integerCoordinateClaim 29 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_17, phase_linear_16_17, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_18 : integerCoordinateClaim 29 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_18, phase_linear_16_18, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_19 : integerCoordinateClaim 29 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_19, phase_linear_16_19, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_20 : integerCoordinateClaim 29 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_20, phase_linear_16_20, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_21 : integerCoordinateClaim 29 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_21, phase_linear_16_21, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_22 : integerCoordinateClaim 29 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_22, phase_linear_16_22, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

private theorem coordinate_29_23 : integerCoordinateClaim 29 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_29]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_29_0, scale_29_1, scale_29_2, scale_29_3, scale_29_4, phase_linear_6_23, phase_linear_16_23, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_29, target_denominator_literal_29, target_numerator_literal_29]
  decide +kernel

theorem integer_residual_029 : integerResidualClaim 29 :=
  (Fin.cases coordinate_29_0 (Fin.cases coordinate_29_1 (Fin.cases coordinate_29_2 (Fin.cases coordinate_29_3 (Fin.cases coordinate_29_4 (Fin.cases coordinate_29_5 (Fin.cases coordinate_29_6 (Fin.cases coordinate_29_7 (Fin.cases coordinate_29_8 (Fin.cases coordinate_29_9 (Fin.cases coordinate_29_10 (Fin.cases coordinate_29_11 (Fin.cases coordinate_29_12 (Fin.cases coordinate_29_13 (Fin.cases coordinate_29_14 (Fin.cases coordinate_29_15 (Fin.cases coordinate_29_16 (Fin.cases coordinate_29_17 (Fin.cases coordinate_29_18 (Fin.cases coordinate_29_19 (Fin.cases coordinate_29_20 (Fin.cases coordinate_29_21 (Fin.cases coordinate_29_22 (Fin.cases coordinate_29_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
