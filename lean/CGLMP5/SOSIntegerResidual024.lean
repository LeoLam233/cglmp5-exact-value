import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear04
import CGLMP5.SOSPhaseLinear14

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_24_0 : commonDenominator 24 / (gramDenominator 55 * phaseDenominator 14) = 147577355847136687501973513343936990517250667040443168750495218589090023883115904435736731852924813140835875094115426889365475423265324966991181793726981770545627381466026823665131866431392250361052567849544847929022149230362957445331821426745015738868737205323144101792334234435604704285478266002903963808472299787860847219372210869539237349926521310654352191308807155819652744068891472868167956214377654941946206426583724192509232762738590 := by
  decide +kernel

private theorem scale_24_1 : commonDenominator 24 / (gramDenominator 99 * phaseDenominator 4) = 1883673171221800411892980764453334804927506379258135744314977376837816917210099373481413184120742330406702044341235949375296910630141206186255477849620306064936476029851379979623992818785671862408885605164583938627658388295833610815038247099636248387685381269219060297127647516372499070114267102228498546563771582614466965388739236492403872798349229535960598 := by
  decide +kernel

private theorem scale_24_2 : commonDenominator 24 / (gramDenominator 108 * phaseDenominator 4) = 1 := by
  decide +kernel

private theorem scale_24_3 : commonDenominator 24 / (gramDenominator 109 * phaseDenominator 4) = 47007312553508663427703404428383135052431653622489947281679562529330904530923315323 := by
  decide +kernel

theorem denominator_divides_024 : ∀ f ∈ fiber 24, commonDenominator 24 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_24_0 : integerCoordinateClaim 24 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_0, phase_linear_14_0, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_1 : integerCoordinateClaim 24 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_1, phase_linear_14_1, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_2 : integerCoordinateClaim 24 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_2, phase_linear_14_2, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_3 : integerCoordinateClaim 24 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_3, phase_linear_14_3, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_4 : integerCoordinateClaim 24 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_4, phase_linear_14_4, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_5 : integerCoordinateClaim 24 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_5, phase_linear_14_5, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_6 : integerCoordinateClaim 24 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_6, phase_linear_14_6, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_7 : integerCoordinateClaim 24 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_7, phase_linear_14_7, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_8 : integerCoordinateClaim 24 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_8, phase_linear_14_8, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_9 : integerCoordinateClaim 24 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_9, phase_linear_14_9, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_10 : integerCoordinateClaim 24 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_10, phase_linear_14_10, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_11 : integerCoordinateClaim 24 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_11, phase_linear_14_11, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_12 : integerCoordinateClaim 24 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_12, phase_linear_14_12, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_13 : integerCoordinateClaim 24 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_13, phase_linear_14_13, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_14 : integerCoordinateClaim 24 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_14, phase_linear_14_14, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_15 : integerCoordinateClaim 24 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_15, phase_linear_14_15, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_16 : integerCoordinateClaim 24 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_16, phase_linear_14_16, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_17 : integerCoordinateClaim 24 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_17, phase_linear_14_17, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_18 : integerCoordinateClaim 24 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_18, phase_linear_14_18, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_19 : integerCoordinateClaim 24 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_19, phase_linear_14_19, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_20 : integerCoordinateClaim 24 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_20, phase_linear_14_20, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_21 : integerCoordinateClaim 24 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_21, phase_linear_14_21, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_22 : integerCoordinateClaim 24 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_22, phase_linear_14_22, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

private theorem coordinate_24_23 : integerCoordinateClaim 24 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_24]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_24_0, scale_24_1, scale_24_2, scale_24_3, phase_linear_4_23, phase_linear_14_23, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_24, target_denominator_literal_24, target_numerator_literal_24]
  decide +kernel

theorem integer_residual_024 : integerResidualClaim 24 :=
  (Fin.cases coordinate_24_0 (Fin.cases coordinate_24_1 (Fin.cases coordinate_24_2 (Fin.cases coordinate_24_3 (Fin.cases coordinate_24_4 (Fin.cases coordinate_24_5 (Fin.cases coordinate_24_6 (Fin.cases coordinate_24_7 (Fin.cases coordinate_24_8 (Fin.cases coordinate_24_9 (Fin.cases coordinate_24_10 (Fin.cases coordinate_24_11 (Fin.cases coordinate_24_12 (Fin.cases coordinate_24_13 (Fin.cases coordinate_24_14 (Fin.cases coordinate_24_15 (Fin.cases coordinate_24_16 (Fin.cases coordinate_24_17 (Fin.cases coordinate_24_18 (Fin.cases coordinate_24_19 (Fin.cases coordinate_24_20 (Fin.cases coordinate_24_21 (Fin.cases coordinate_24_22 (Fin.cases coordinate_24_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
