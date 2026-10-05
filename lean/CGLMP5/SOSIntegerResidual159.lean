import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear06
import CGLMP5.SOSPhaseLinear16

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_159_0 : commonDenominator 159 / (gramDenominator 55 * phaseDenominator 6) = 147577355847136687501973513343936990517250667040443168750495218589090023883115904435736731852924813140835875094115426889365475423265324966991181793726981770545627381466026823665131866431392250361052567849544847929022149230362957445331821426745015738868737205323144101792334234435604704285478266002903963808472299787860847219372210869539237349926521310654352191308807155819652744068891472868167956214377654941946206426583724192509232762738590 := by
  decide +kernel

private theorem scale_159_1 : commonDenominator 159 / (gramDenominator 99 * phaseDenominator 16) = 1883673171221800411892980764453334804927506379258135744314977376837816917210099373481413184120742330406702044341235949375296910630141206186255477849620306064936476029851379979623992818785671862408885605164583938627658388295833610815038247099636248387685381269219060297127647516372499070114267102228498546563771582614466965388739236492403872798349229535960598 := by
  decide +kernel

private theorem scale_159_2 : commonDenominator 159 / (gramDenominator 108 * phaseDenominator 16) = 1 := by
  decide +kernel

private theorem scale_159_3 : commonDenominator 159 / (gramDenominator 109 * phaseDenominator 16) = 47007312553508663427703404428383135052431653622489947281679562529330904530923315323 := by
  decide +kernel

theorem denominator_divides_159 : ∀ f ∈ fiber 159, commonDenominator 159 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_159_0 : integerCoordinateClaim 159 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_0, phase_linear_16_0, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_1 : integerCoordinateClaim 159 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_1, phase_linear_16_1, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_2 : integerCoordinateClaim 159 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_2, phase_linear_16_2, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_3 : integerCoordinateClaim 159 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_3, phase_linear_16_3, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_4 : integerCoordinateClaim 159 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_4, phase_linear_16_4, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_5 : integerCoordinateClaim 159 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_5, phase_linear_16_5, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_6 : integerCoordinateClaim 159 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_6, phase_linear_16_6, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_7 : integerCoordinateClaim 159 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_7, phase_linear_16_7, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_8 : integerCoordinateClaim 159 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_8, phase_linear_16_8, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_9 : integerCoordinateClaim 159 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_9, phase_linear_16_9, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_10 : integerCoordinateClaim 159 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_10, phase_linear_16_10, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_11 : integerCoordinateClaim 159 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_11, phase_linear_16_11, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_12 : integerCoordinateClaim 159 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_12, phase_linear_16_12, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_13 : integerCoordinateClaim 159 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_13, phase_linear_16_13, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_14 : integerCoordinateClaim 159 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_14, phase_linear_16_14, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_15 : integerCoordinateClaim 159 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_15, phase_linear_16_15, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_16 : integerCoordinateClaim 159 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_16, phase_linear_16_16, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_17 : integerCoordinateClaim 159 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_17, phase_linear_16_17, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_18 : integerCoordinateClaim 159 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_18, phase_linear_16_18, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_19 : integerCoordinateClaim 159 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_19, phase_linear_16_19, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_20 : integerCoordinateClaim 159 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_20, phase_linear_16_20, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_21 : integerCoordinateClaim 159 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_21, phase_linear_16_21, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_22 : integerCoordinateClaim 159 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_22, phase_linear_16_22, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

private theorem coordinate_159_23 : integerCoordinateClaim 159 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_159]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_159_0, scale_159_1, scale_159_2, scale_159_3, phase_linear_6_23, phase_linear_16_23, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_159, target_denominator_literal_159, target_numerator_literal_159]
  decide +kernel

theorem integer_residual_159 : integerResidualClaim 159 :=
  (Fin.cases coordinate_159_0 (Fin.cases coordinate_159_1 (Fin.cases coordinate_159_2 (Fin.cases coordinate_159_3 (Fin.cases coordinate_159_4 (Fin.cases coordinate_159_5 (Fin.cases coordinate_159_6 (Fin.cases coordinate_159_7 (Fin.cases coordinate_159_8 (Fin.cases coordinate_159_9 (Fin.cases coordinate_159_10 (Fin.cases coordinate_159_11 (Fin.cases coordinate_159_12 (Fin.cases coordinate_159_13 (Fin.cases coordinate_159_14 (Fin.cases coordinate_159_15 (Fin.cases coordinate_159_16 (Fin.cases coordinate_159_17 (Fin.cases coordinate_159_18 (Fin.cases coordinate_159_19 (Fin.cases coordinate_159_20 (Fin.cases coordinate_159_21 (Fin.cases coordinate_159_22 (Fin.cases coordinate_159_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
