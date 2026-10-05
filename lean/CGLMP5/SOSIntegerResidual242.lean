import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear04
import CGLMP5.SOSPhaseLinear14

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_242_0 : commonDenominator 242 / (gramDenominator 55 * phaseDenominator 14) = 147577355847136687501973513343936990517250667040443168750495218589090023883115904435736731852924813140835875094115426889365475423265324966991181793726981770545627381466026823665131866431392250361052567849544847929022149230362957445331821426745015738868737205323144101792334234435604704285478266002903963808472299787860847219372210869539237349926521310654352191308807155819652744068891472868167956214377654941946206426583724192509232762738590 := by
  decide +kernel

private theorem scale_242_1 : commonDenominator 242 / (gramDenominator 99 * phaseDenominator 4) = 1883673171221800411892980764453334804927506379258135744314977376837816917210099373481413184120742330406702044341235949375296910630141206186255477849620306064936476029851379979623992818785671862408885605164583938627658388295833610815038247099636248387685381269219060297127647516372499070114267102228498546563771582614466965388739236492403872798349229535960598 := by
  decide +kernel

private theorem scale_242_2 : commonDenominator 242 / (gramDenominator 108 * phaseDenominator 4) = 1 := by
  decide +kernel

private theorem scale_242_3 : commonDenominator 242 / (gramDenominator 109 * phaseDenominator 4) = 47007312553508663427703404428383135052431653622489947281679562529330904530923315323 := by
  decide +kernel

theorem denominator_divides_242 : ∀ f ∈ fiber 242, commonDenominator 242 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_242_0 : integerCoordinateClaim 242 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_0, phase_linear_14_0, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_1 : integerCoordinateClaim 242 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_1, phase_linear_14_1, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_2 : integerCoordinateClaim 242 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_2, phase_linear_14_2, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_3 : integerCoordinateClaim 242 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_3, phase_linear_14_3, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_4 : integerCoordinateClaim 242 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_4, phase_linear_14_4, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_5 : integerCoordinateClaim 242 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_5, phase_linear_14_5, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_6 : integerCoordinateClaim 242 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_6, phase_linear_14_6, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_7 : integerCoordinateClaim 242 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_7, phase_linear_14_7, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_8 : integerCoordinateClaim 242 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_8, phase_linear_14_8, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_9 : integerCoordinateClaim 242 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_9, phase_linear_14_9, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_10 : integerCoordinateClaim 242 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_10, phase_linear_14_10, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_11 : integerCoordinateClaim 242 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_11, phase_linear_14_11, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_12 : integerCoordinateClaim 242 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_12, phase_linear_14_12, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_13 : integerCoordinateClaim 242 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_13, phase_linear_14_13, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_14 : integerCoordinateClaim 242 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_14, phase_linear_14_14, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_15 : integerCoordinateClaim 242 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_15, phase_linear_14_15, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_16 : integerCoordinateClaim 242 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_16, phase_linear_14_16, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_17 : integerCoordinateClaim 242 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_17, phase_linear_14_17, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_18 : integerCoordinateClaim 242 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_18, phase_linear_14_18, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_19 : integerCoordinateClaim 242 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_19, phase_linear_14_19, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_20 : integerCoordinateClaim 242 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_20, phase_linear_14_20, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_21 : integerCoordinateClaim 242 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_21, phase_linear_14_21, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_22 : integerCoordinateClaim 242 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_22, phase_linear_14_22, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

private theorem coordinate_242_23 : integerCoordinateClaim 242 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_242]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_242_0, scale_242_1, scale_242_2, scale_242_3, phase_linear_4_23, phase_linear_14_23, gram_numerator_literal_55, gram_numerator_literal_99, gram_numerator_literal_108, gram_numerator_literal_109, denominator_literal_242, target_denominator_literal_242, target_numerator_literal_242]
  decide +kernel

theorem integer_residual_242 : integerResidualClaim 242 :=
  (Fin.cases coordinate_242_0 (Fin.cases coordinate_242_1 (Fin.cases coordinate_242_2 (Fin.cases coordinate_242_3 (Fin.cases coordinate_242_4 (Fin.cases coordinate_242_5 (Fin.cases coordinate_242_6 (Fin.cases coordinate_242_7 (Fin.cases coordinate_242_8 (Fin.cases coordinate_242_9 (Fin.cases coordinate_242_10 (Fin.cases coordinate_242_11 (Fin.cases coordinate_242_12 (Fin.cases coordinate_242_13 (Fin.cases coordinate_242_14 (Fin.cases coordinate_242_15 (Fin.cases coordinate_242_16 (Fin.cases coordinate_242_17 (Fin.cases coordinate_242_18 (Fin.cases coordinate_242_19 (Fin.cases coordinate_242_20 (Fin.cases coordinate_242_21 (Fin.cases coordinate_242_22 (Fin.cases coordinate_242_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
