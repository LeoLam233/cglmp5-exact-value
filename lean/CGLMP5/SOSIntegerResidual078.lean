import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear08
import CGLMP5.SOSPhaseLinear18

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_78_0 : commonDenominator 78 / (gramDenominator 5 * phaseDenominator 18) = 100369001 := by
  decide +kernel

private theorem scale_78_1 : commonDenominator 78 / (gramDenominator 24 * phaseDenominator 18) = 100369001 := by
  decide +kernel

private theorem scale_78_2 : commonDenominator 78 / (gramDenominator 30 * phaseDenominator 8) = 282533695810370305397573962301632765641524605166676308007703342454610555666755721133439691276975000332944549868372677775445957179538589240230822246048172488206576874696286142653651546132733034121859090516687189701968502392970314622042546720415538142979538960 := by
  decide +kernel

private theorem scale_78_3 : commonDenominator 78 / (gramDenominator 41 * phaseDenominator 8) = 17755622709080687925229049511253634592694693224369207183369266516301182566538775562770142123161742353018112827245165707505747191924849549393244491152097009471998008843722532770731676 := by
  decide +kernel

private theorem scale_78_4 : commonDenominator 78 / (gramDenominator 110 * phaseDenominator 18) = 445528528360835568862000598906016390421952064232851545039199273585974977330528232749612989382440760347954329843970716035452511853013104086975026431422328973947994405408398933847025089793919 := by
  decide +kernel

theorem denominator_divides_078 : ∀ f ∈ fiber 78, commonDenominator 78 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_78_0 : integerCoordinateClaim 78 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_0, phase_linear_18_0, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_1 : integerCoordinateClaim 78 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_1, phase_linear_18_1, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_2 : integerCoordinateClaim 78 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_2, phase_linear_18_2, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_3 : integerCoordinateClaim 78 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_3, phase_linear_18_3, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_4 : integerCoordinateClaim 78 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_4, phase_linear_18_4, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_5 : integerCoordinateClaim 78 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_5, phase_linear_18_5, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_6 : integerCoordinateClaim 78 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_6, phase_linear_18_6, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_7 : integerCoordinateClaim 78 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_7, phase_linear_18_7, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_8 : integerCoordinateClaim 78 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_8, phase_linear_18_8, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_9 : integerCoordinateClaim 78 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_9, phase_linear_18_9, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_10 : integerCoordinateClaim 78 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_10, phase_linear_18_10, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_11 : integerCoordinateClaim 78 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_11, phase_linear_18_11, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_12 : integerCoordinateClaim 78 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_12, phase_linear_18_12, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_13 : integerCoordinateClaim 78 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_13, phase_linear_18_13, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_14 : integerCoordinateClaim 78 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_14, phase_linear_18_14, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_15 : integerCoordinateClaim 78 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_15, phase_linear_18_15, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_16 : integerCoordinateClaim 78 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_16, phase_linear_18_16, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_17 : integerCoordinateClaim 78 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_17, phase_linear_18_17, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_18 : integerCoordinateClaim 78 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_18, phase_linear_18_18, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_19 : integerCoordinateClaim 78 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_19, phase_linear_18_19, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_20 : integerCoordinateClaim 78 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_20, phase_linear_18_20, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_21 : integerCoordinateClaim 78 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_21, phase_linear_18_21, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_22 : integerCoordinateClaim 78 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_22, phase_linear_18_22, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

private theorem coordinate_78_23 : integerCoordinateClaim 78 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_78]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_78_0, scale_78_1, scale_78_2, scale_78_3, scale_78_4, phase_linear_8_23, phase_linear_18_23, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_78, target_denominator_literal_78, target_numerator_literal_78]
  decide +kernel

theorem integer_residual_078 : integerResidualClaim 78 :=
  (Fin.cases coordinate_78_0 (Fin.cases coordinate_78_1 (Fin.cases coordinate_78_2 (Fin.cases coordinate_78_3 (Fin.cases coordinate_78_4 (Fin.cases coordinate_78_5 (Fin.cases coordinate_78_6 (Fin.cases coordinate_78_7 (Fin.cases coordinate_78_8 (Fin.cases coordinate_78_9 (Fin.cases coordinate_78_10 (Fin.cases coordinate_78_11 (Fin.cases coordinate_78_12 (Fin.cases coordinate_78_13 (Fin.cases coordinate_78_14 (Fin.cases coordinate_78_15 (Fin.cases coordinate_78_16 (Fin.cases coordinate_78_17 (Fin.cases coordinate_78_18 (Fin.cases coordinate_78_19 (Fin.cases coordinate_78_20 (Fin.cases coordinate_78_21 (Fin.cases coordinate_78_22 (Fin.cases coordinate_78_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
