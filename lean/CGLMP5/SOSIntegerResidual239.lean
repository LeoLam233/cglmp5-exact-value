import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear00
import CGLMP5.SOSPhaseLinear10

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_239_0 : commonDenominator 239 / (gramDenominator 55 * phaseDenominator 10) = 147577355847136687501973513343936990517250667040443168750495218589090023883115904435736731852924813140835875094115426889365475423265324966991181793726981770545627381466026823665131866431392250361052567849544847929022149230362957445331821426745015738868737205323144101792334234435604704285478266002903963808472299787860847219372210869539237349926521310654352191308807155819652744068891472868167956214377654941946206426583724192509232762738590 := by
  decide +kernel

private theorem scale_239_1 : commonDenominator 239 / (gramDenominator 99 * phaseDenominator 0) = 1883673171221800411892980764453334804927506379258135744314977376837816917210099373481413184120742330406702044341235949375296910630141206186255477849620306064936476029851379979623992818785671862408885605164583938627658388295833610815038247099636248387685381269219060297127647516372499070114267102228498546563771582614466965388739236492403872798349229535960598 := by
  decide +kernel

private theorem scale_239_2 : commonDenominator 239 / (gramDenominator 108 * phaseDenominator 0) = 1 := by
  decide +kernel

private theorem scale_239_3 : commonDenominator 239 / (gramDenominator 109 * phaseDenominator 0) = 47007312553508663427703404428383135052431653622489947281679562529330904530923315323 := by
  decide +kernel

theorem denominator_divides_239 : ∀ f ∈ fiber 239, commonDenominator 239 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_239_0 : integerCoordinateClaim 239 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_0, phase_linear_10_0, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_1 : integerCoordinateClaim 239 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_1, phase_linear_10_1, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_2 : integerCoordinateClaim 239 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_2, phase_linear_10_2, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_3 : integerCoordinateClaim 239 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_3, phase_linear_10_3, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_4 : integerCoordinateClaim 239 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_4, phase_linear_10_4, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_5 : integerCoordinateClaim 239 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_5, phase_linear_10_5, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_6 : integerCoordinateClaim 239 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_6, phase_linear_10_6, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_7 : integerCoordinateClaim 239 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_7, phase_linear_10_7, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_8 : integerCoordinateClaim 239 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_8, phase_linear_10_8, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_9 : integerCoordinateClaim 239 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_9, phase_linear_10_9, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_10 : integerCoordinateClaim 239 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_10, phase_linear_10_10, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_11 : integerCoordinateClaim 239 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_11, phase_linear_10_11, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_12 : integerCoordinateClaim 239 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_12, phase_linear_10_12, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_13 : integerCoordinateClaim 239 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_13, phase_linear_10_13, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_14 : integerCoordinateClaim 239 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_14, phase_linear_10_14, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_15 : integerCoordinateClaim 239 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_15, phase_linear_10_15, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_16 : integerCoordinateClaim 239 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_16, phase_linear_10_16, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_17 : integerCoordinateClaim 239 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_17, phase_linear_10_17, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_18 : integerCoordinateClaim 239 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_18, phase_linear_10_18, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_19 : integerCoordinateClaim 239 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_19, phase_linear_10_19, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_20 : integerCoordinateClaim 239 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_20, phase_linear_10_20, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_21 : integerCoordinateClaim 239 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_21, phase_linear_10_21, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_22 : integerCoordinateClaim 239 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_22, phase_linear_10_22, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

private theorem coordinate_239_23 : integerCoordinateClaim 239 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_239]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_239_0, scale_239_1, scale_239_2, scale_239_3, phase_linear_0_23, phase_linear_10_23, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_239, target_denominator_literal_239, target_numerator_literal_239]
  decide +kernel

theorem integer_residual_239 : integerResidualClaim 239 :=
  (Fin.cases coordinate_239_0 (Fin.cases coordinate_239_1 (Fin.cases coordinate_239_2 (Fin.cases coordinate_239_3 (Fin.cases coordinate_239_4 (Fin.cases coordinate_239_5 (Fin.cases coordinate_239_6 (Fin.cases coordinate_239_7 (Fin.cases coordinate_239_8 (Fin.cases coordinate_239_9 (Fin.cases coordinate_239_10 (Fin.cases coordinate_239_11 (Fin.cases coordinate_239_12 (Fin.cases coordinate_239_13 (Fin.cases coordinate_239_14 (Fin.cases coordinate_239_15 (Fin.cases coordinate_239_16 (Fin.cases coordinate_239_17 (Fin.cases coordinate_239_18 (Fin.cases coordinate_239_19 (Fin.cases coordinate_239_20 (Fin.cases coordinate_239_21 (Fin.cases coordinate_239_22 (Fin.cases coordinate_239_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
