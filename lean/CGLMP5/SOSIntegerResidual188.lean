import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear08
import CGLMP5.SOSPhaseLinear18

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_188_0 : commonDenominator 188 / (gramDenominator 5 * phaseDenominator 18) = 100369001 := by
  decide +kernel

private theorem scale_188_1 : commonDenominator 188 / (gramDenominator 24 * phaseDenominator 18) = 100369001 := by
  decide +kernel

private theorem scale_188_2 : commonDenominator 188 / (gramDenominator 30 * phaseDenominator 8) = 282533695810370305397573962301632765641524605166676308007703342454610555666755721133439691276975000332944549868372677775445957179538589240230822246048172488206576874696286142653651546132733034121859090516687189701968502392970314622042546720415538142979538960 := by
  decide +kernel

private theorem scale_188_3 : commonDenominator 188 / (gramDenominator 41 * phaseDenominator 8) = 17755622709080687925229049511253634592694693224369207183369266516301182566538775562770142123161742353018112827245165707505747191924849549393244491152097009471998008843722532770731676 := by
  decide +kernel

private theorem scale_188_4 : commonDenominator 188 / (gramDenominator 110 * phaseDenominator 18) = 445528528360835568862000598906016390421952064232851545039199273585974977330528232749612989382440760347954329843970716035452511853013104086975026431422328973947994405408398933847025089793919 := by
  decide +kernel

theorem denominator_divides_188 : ∀ f ∈ fiber 188, commonDenominator 188 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_188_0 : integerCoordinateClaim 188 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_0, phase_linear_18_0, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_1 : integerCoordinateClaim 188 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_1, phase_linear_18_1, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_2 : integerCoordinateClaim 188 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_2, phase_linear_18_2, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_3 : integerCoordinateClaim 188 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_3, phase_linear_18_3, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_4 : integerCoordinateClaim 188 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_4, phase_linear_18_4, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_5 : integerCoordinateClaim 188 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_5, phase_linear_18_5, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_6 : integerCoordinateClaim 188 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_6, phase_linear_18_6, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_7 : integerCoordinateClaim 188 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_7, phase_linear_18_7, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_8 : integerCoordinateClaim 188 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_8, phase_linear_18_8, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_9 : integerCoordinateClaim 188 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_9, phase_linear_18_9, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_10 : integerCoordinateClaim 188 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_10, phase_linear_18_10, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_11 : integerCoordinateClaim 188 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_11, phase_linear_18_11, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_12 : integerCoordinateClaim 188 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_12, phase_linear_18_12, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_13 : integerCoordinateClaim 188 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_13, phase_linear_18_13, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_14 : integerCoordinateClaim 188 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_14, phase_linear_18_14, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_15 : integerCoordinateClaim 188 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_15, phase_linear_18_15, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_16 : integerCoordinateClaim 188 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_16, phase_linear_18_16, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_17 : integerCoordinateClaim 188 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_17, phase_linear_18_17, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_18 : integerCoordinateClaim 188 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_18, phase_linear_18_18, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_19 : integerCoordinateClaim 188 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_19, phase_linear_18_19, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_20 : integerCoordinateClaim 188 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_20, phase_linear_18_20, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_21 : integerCoordinateClaim 188 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_21, phase_linear_18_21, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_22 : integerCoordinateClaim 188 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_22, phase_linear_18_22, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

private theorem coordinate_188_23 : integerCoordinateClaim 188 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_188]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_188_0, scale_188_1, scale_188_2, scale_188_3, scale_188_4, phase_linear_8_23, phase_linear_18_23, gram_numerator_literal_5, gram_numerator_literal_24, gram_numerator_literal_30, gram_numerator_literal_41, gram_numerator_literal_110, denominator_literal_188, target_denominator_literal_188, target_numerator_literal_188]
  decide +kernel

theorem integer_residual_188 : integerResidualClaim 188 :=
  (Fin.cases coordinate_188_0 (Fin.cases coordinate_188_1 (Fin.cases coordinate_188_2 (Fin.cases coordinate_188_3 (Fin.cases coordinate_188_4 (Fin.cases coordinate_188_5 (Fin.cases coordinate_188_6 (Fin.cases coordinate_188_7 (Fin.cases coordinate_188_8 (Fin.cases coordinate_188_9 (Fin.cases coordinate_188_10 (Fin.cases coordinate_188_11 (Fin.cases coordinate_188_12 (Fin.cases coordinate_188_13 (Fin.cases coordinate_188_14 (Fin.cases coordinate_188_15 (Fin.cases coordinate_188_16 (Fin.cases coordinate_188_17 (Fin.cases coordinate_188_18 (Fin.cases coordinate_188_19 (Fin.cases coordinate_188_20 (Fin.cases coordinate_188_21 (Fin.cases coordinate_188_22 (Fin.cases coordinate_188_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
