import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear02
import CGLMP5.SOSPhaseLinear12

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_213_0 : commonDenominator 213 / (gramDenominator 5 * phaseDenominator 2) = 100369001 := by
  decide +kernel

private theorem scale_213_1 : commonDenominator 213 / (gramDenominator 24 * phaseDenominator 2) = 100369001 := by
  decide +kernel

private theorem scale_213_2 : commonDenominator 213 / (gramDenominator 30 * phaseDenominator 12) = 282533695810370305397573962301632765641524605166676308007703342454610555666755721133439691276975000332944549868372677775445957179538589240230822246048172488206576874696286142653651546132733034121859090516687189701968502392970314622042546720415538142979538960 := by
  decide +kernel

private theorem scale_213_3 : commonDenominator 213 / (gramDenominator 41 * phaseDenominator 12) = 17755622709080687925229049511253634592694693224369207183369266516301182566538775562770142123161742353018112827245165707505747191924849549393244491152097009471998008843722532770731676 := by
  decide +kernel

private theorem scale_213_4 : commonDenominator 213 / (gramDenominator 110 * phaseDenominator 2) = 445528528360835568862000598906016390421952064232851545039199273585974977330528232749612989382440760347954329843970716035452511853013104086975026431422328973947994405408398933847025089793919 := by
  decide +kernel

theorem denominator_divides_213 : ∀ f ∈ fiber 213, commonDenominator 213 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_213_0 : integerCoordinateClaim 213 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_0, phase_linear_12_0, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_1 : integerCoordinateClaim 213 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_1, phase_linear_12_1, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_2 : integerCoordinateClaim 213 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_2, phase_linear_12_2, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_3 : integerCoordinateClaim 213 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_3, phase_linear_12_3, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_4 : integerCoordinateClaim 213 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_4, phase_linear_12_4, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_5 : integerCoordinateClaim 213 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_5, phase_linear_12_5, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_6 : integerCoordinateClaim 213 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_6, phase_linear_12_6, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_7 : integerCoordinateClaim 213 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_7, phase_linear_12_7, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_8 : integerCoordinateClaim 213 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_8, phase_linear_12_8, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_9 : integerCoordinateClaim 213 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_9, phase_linear_12_9, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_10 : integerCoordinateClaim 213 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_10, phase_linear_12_10, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_11 : integerCoordinateClaim 213 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_11, phase_linear_12_11, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_12 : integerCoordinateClaim 213 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_12, phase_linear_12_12, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_13 : integerCoordinateClaim 213 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_13, phase_linear_12_13, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_14 : integerCoordinateClaim 213 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_14, phase_linear_12_14, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_15 : integerCoordinateClaim 213 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_15, phase_linear_12_15, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_16 : integerCoordinateClaim 213 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_16, phase_linear_12_16, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_17 : integerCoordinateClaim 213 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_17, phase_linear_12_17, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_18 : integerCoordinateClaim 213 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_18, phase_linear_12_18, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_19 : integerCoordinateClaim 213 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_19, phase_linear_12_19, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_20 : integerCoordinateClaim 213 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_20, phase_linear_12_20, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_21 : integerCoordinateClaim 213 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_21, phase_linear_12_21, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_22 : integerCoordinateClaim 213 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_22, phase_linear_12_22, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

private theorem coordinate_213_23 : integerCoordinateClaim 213 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_213]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_213_0, scale_213_1, scale_213_2, scale_213_3, scale_213_4, phase_linear_2_23, phase_linear_12_23, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_213, target_denominator_literal_213, target_numerator_literal_213]
  decide +kernel

theorem integer_residual_213 : integerResidualClaim 213 :=
  (Fin.cases coordinate_213_0 (Fin.cases coordinate_213_1 (Fin.cases coordinate_213_2 (Fin.cases coordinate_213_3 (Fin.cases coordinate_213_4 (Fin.cases coordinate_213_5 (Fin.cases coordinate_213_6 (Fin.cases coordinate_213_7 (Fin.cases coordinate_213_8 (Fin.cases coordinate_213_9 (Fin.cases coordinate_213_10 (Fin.cases coordinate_213_11 (Fin.cases coordinate_213_12 (Fin.cases coordinate_213_13 (Fin.cases coordinate_213_14 (Fin.cases coordinate_213_15 (Fin.cases coordinate_213_16 (Fin.cases coordinate_213_17 (Fin.cases coordinate_213_18 (Fin.cases coordinate_213_19 (Fin.cases coordinate_213_20 (Fin.cases coordinate_213_21 (Fin.cases coordinate_213_22 (Fin.cases coordinate_213_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
