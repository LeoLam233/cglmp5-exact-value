import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear10
import CGLMP5.SOSPhaseLinear15

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_88_0 : commonDenominator 88 / (gramDenominator 11 * phaseDenominator 15) = 2362303436024831191292969575489110849898833974934561978410086535948080216576439044247825372052047273289195908517170282806143302294457738369580764227408815255061863460970885387150199924817250846162693365934802728572047586163010186963486546611345474859932898296527602063268556049726134389598750353154868225053042208644172955141184891433163623064505444943972887645896833659028963920473481999686976556933270363161176192232929974099087799135334293052821917855631887832425185605 := by
  decide +kernel

private theorem scale_88_1 : commonDenominator 88 / (gramDenominator 36 * phaseDenominator 10) = 4607106699159127806861348734270062050410539120697327583901607524546005272316525344630640875371798621459505500924034994608982386192052693139282968624933209170995701798365448106058754849259272610414222498605126693024072661002164522832700388143053053532078638315418544484416733035399069568439211629582901410012417703264759797771986764466567167607689969782678030078464409182011657243190000070571188462284691274745846235747821733938463791330952372509741662443919873425687582124831921691850542467538736218243643692292716548 := by
  decide +kernel

private theorem scale_88_2 : commonDenominator 88 / (gramDenominator 46 * phaseDenominator 10) = 79199862280618519798273268966545365881205511045012640188636787778976385318017244126454655389943874873847973247939695338867737414126780092921890106687092609327670293347333299155464722 := by
  decide +kernel

private theorem scale_88_3 : commonDenominator 88 / (gramDenominator 51 * phaseDenominator 10) = 7949211056443262494251409531176460794676081819282384728105925941224868596960458093745371433287932167157122100770432529406511275386228205273257281039966904792701549000648789250268137837882722 := by
  decide +kernel

private theorem scale_88_4 : commonDenominator 88 / (gramDenominator 124 * phaseDenominator 10) = 59654230903957640817769819277896287578604635305525125408460348247878310879294073301919235829211405665347292463138348954342992008558554988309086468828611807460880367224940016403884022569097634541670308101159429483386188413747803166714371984886194773728775140015112988577591279707152038035805 := by
  decide +kernel

private theorem scale_88_5 : commonDenominator 88 / (gramDenominator 128 * phaseDenominator 10) = 59654230903957640817769819277896287578604635305525125408460348247878310879294073301919235829211405665347292463138348954342992008558554988309086468828611807460880367224940016403884022569097634541670308101159429483386188413747803166714371984886194773728775140015112988577591279707152038035805 := by
  decide +kernel

theorem denominator_divides_088 : ∀ f ∈ fiber 88, commonDenominator 88 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_88_0 : integerCoordinateClaim 88 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_0, phase_linear_15_0, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_1 : integerCoordinateClaim 88 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_1, phase_linear_15_1, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_2 : integerCoordinateClaim 88 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_2, phase_linear_15_2, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_3 : integerCoordinateClaim 88 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_3, phase_linear_15_3, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_4 : integerCoordinateClaim 88 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_4, phase_linear_15_4, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_5 : integerCoordinateClaim 88 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_5, phase_linear_15_5, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_6 : integerCoordinateClaim 88 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_6, phase_linear_15_6, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_7 : integerCoordinateClaim 88 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_7, phase_linear_15_7, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_8 : integerCoordinateClaim 88 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_8, phase_linear_15_8, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_9 : integerCoordinateClaim 88 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_9, phase_linear_15_9, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_10 : integerCoordinateClaim 88 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_10, phase_linear_15_10, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_11 : integerCoordinateClaim 88 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_11, phase_linear_15_11, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_12 : integerCoordinateClaim 88 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_12, phase_linear_15_12, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_13 : integerCoordinateClaim 88 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_13, phase_linear_15_13, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_14 : integerCoordinateClaim 88 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_14, phase_linear_15_14, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_15 : integerCoordinateClaim 88 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_15, phase_linear_15_15, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_16 : integerCoordinateClaim 88 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_16, phase_linear_15_16, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_17 : integerCoordinateClaim 88 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_17, phase_linear_15_17, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_18 : integerCoordinateClaim 88 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_18, phase_linear_15_18, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_19 : integerCoordinateClaim 88 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_19, phase_linear_15_19, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_20 : integerCoordinateClaim 88 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_20, phase_linear_15_20, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_21 : integerCoordinateClaim 88 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_21, phase_linear_15_21, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_22 : integerCoordinateClaim 88 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_22, phase_linear_15_22, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

private theorem coordinate_88_23 : integerCoordinateClaim 88 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_88]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_88_0, scale_88_1, scale_88_2, scale_88_3, scale_88_4, scale_88_5, phase_linear_10_23, phase_linear_15_23, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_88, target_denominator_literal_88, target_numerator_literal_88]
  decide +kernel

theorem integer_residual_088 : integerResidualClaim 88 :=
  (Fin.cases coordinate_88_0 (Fin.cases coordinate_88_1 (Fin.cases coordinate_88_2 (Fin.cases coordinate_88_3 (Fin.cases coordinate_88_4 (Fin.cases coordinate_88_5 (Fin.cases coordinate_88_6 (Fin.cases coordinate_88_7 (Fin.cases coordinate_88_8 (Fin.cases coordinate_88_9 (Fin.cases coordinate_88_10 (Fin.cases coordinate_88_11 (Fin.cases coordinate_88_12 (Fin.cases coordinate_88_13 (Fin.cases coordinate_88_14 (Fin.cases coordinate_88_15 (Fin.cases coordinate_88_16 (Fin.cases coordinate_88_17 (Fin.cases coordinate_88_18 (Fin.cases coordinate_88_19 (Fin.cases coordinate_88_20 (Fin.cases coordinate_88_21 (Fin.cases coordinate_88_22 (Fin.cases coordinate_88_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
