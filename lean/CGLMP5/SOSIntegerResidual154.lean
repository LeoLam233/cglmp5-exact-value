import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear02
import CGLMP5.SOSPhaseLinear07

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_154_0 : commonDenominator 154 / (gramDenominator 11 * phaseDenominator 7) = 2362303436024831191292969575489110849898833974934561978410086535948080216576439044247825372052047273289195908517170282806143302294457738369580764227408815255061863460970885387150199924817250846162693365934802728572047586163010186963486546611345474859932898296527602063268556049726134389598750353154868225053042208644172955141184891433163623064505444943972887645896833659028963920473481999686976556933270363161176192232929974099087799135334293052821917855631887832425185605 := by
  decide +kernel

private theorem scale_154_1 : commonDenominator 154 / (gramDenominator 36 * phaseDenominator 2) = 4607106699159127806861348734270062050410539120697327583901607524546005272316525344630640875371798621459505500924034994608982386192052693139282968624933209170995701798365448106058754849259272610414222498605126693024072661002164522832700388143053053532078638315418544484416733035399069568439211629582901410012417703264759797771986764466567167607689969782678030078464409182011657243190000070571188462284691274745846235747821733938463791330952372509741662443919873425687582124831921691850542467538736218243643692292716548 := by
  decide +kernel

private theorem scale_154_2 : commonDenominator 154 / (gramDenominator 46 * phaseDenominator 2) = 79199862280618519798273268966545365881205511045012640188636787778976385318017244126454655389943874873847973247939695338867737414126780092921890106687092609327670293347333299155464722 := by
  decide +kernel

private theorem scale_154_3 : commonDenominator 154 / (gramDenominator 51 * phaseDenominator 2) = 7949211056443262494251409531176460794676081819282384728105925941224868596960458093745371433287932167157122100770432529406511275386228205273257281039966904792701549000648789250268137837882722 := by
  decide +kernel

private theorem scale_154_4 : commonDenominator 154 / (gramDenominator 124 * phaseDenominator 2) = 59654230903957640817769819277896287578604635305525125408460348247878310879294073301919235829211405665347292463138348954342992008558554988309086468828611807460880367224940016403884022569097634541670308101159429483386188413747803166714371984886194773728775140015112988577591279707152038035805 := by
  decide +kernel

private theorem scale_154_5 : commonDenominator 154 / (gramDenominator 128 * phaseDenominator 2) = 59654230903957640817769819277896287578604635305525125408460348247878310879294073301919235829211405665347292463138348954342992008558554988309086468828611807460880367224940016403884022569097634541670308101159429483386188413747803166714371984886194773728775140015112988577591279707152038035805 := by
  decide +kernel

theorem denominator_divides_154 : ∀ f ∈ fiber 154, commonDenominator 154 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_154_0 : integerCoordinateClaim 154 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_0, phase_linear_7_0, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_1 : integerCoordinateClaim 154 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_1, phase_linear_7_1, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_2 : integerCoordinateClaim 154 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_2, phase_linear_7_2, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_3 : integerCoordinateClaim 154 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_3, phase_linear_7_3, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_4 : integerCoordinateClaim 154 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_4, phase_linear_7_4, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_5 : integerCoordinateClaim 154 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_5, phase_linear_7_5, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_6 : integerCoordinateClaim 154 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_6, phase_linear_7_6, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_7 : integerCoordinateClaim 154 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_7, phase_linear_7_7, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_8 : integerCoordinateClaim 154 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_8, phase_linear_7_8, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_9 : integerCoordinateClaim 154 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_9, phase_linear_7_9, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_10 : integerCoordinateClaim 154 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_10, phase_linear_7_10, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_11 : integerCoordinateClaim 154 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_11, phase_linear_7_11, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_12 : integerCoordinateClaim 154 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_12, phase_linear_7_12, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_13 : integerCoordinateClaim 154 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_13, phase_linear_7_13, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_14 : integerCoordinateClaim 154 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_14, phase_linear_7_14, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_15 : integerCoordinateClaim 154 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_15, phase_linear_7_15, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_16 : integerCoordinateClaim 154 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_16, phase_linear_7_16, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_17 : integerCoordinateClaim 154 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_17, phase_linear_7_17, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_18 : integerCoordinateClaim 154 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_18, phase_linear_7_18, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_19 : integerCoordinateClaim 154 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_19, phase_linear_7_19, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_20 : integerCoordinateClaim 154 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_20, phase_linear_7_20, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_21 : integerCoordinateClaim 154 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_21, phase_linear_7_21, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_22 : integerCoordinateClaim 154 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_22, phase_linear_7_22, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

private theorem coordinate_154_23 : integerCoordinateClaim 154 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_154]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_154_0, scale_154_1, scale_154_2, scale_154_3, scale_154_4, scale_154_5, phase_linear_2_23, phase_linear_7_23, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_154, target_denominator_literal_154, target_numerator_literal_154]
  decide +kernel

theorem integer_residual_154 : integerResidualClaim 154 :=
  (Fin.cases coordinate_154_0 (Fin.cases coordinate_154_1 (Fin.cases coordinate_154_2 (Fin.cases coordinate_154_3 (Fin.cases coordinate_154_4 (Fin.cases coordinate_154_5 (Fin.cases coordinate_154_6 (Fin.cases coordinate_154_7 (Fin.cases coordinate_154_8 (Fin.cases coordinate_154_9 (Fin.cases coordinate_154_10 (Fin.cases coordinate_154_11 (Fin.cases coordinate_154_12 (Fin.cases coordinate_154_13 (Fin.cases coordinate_154_14 (Fin.cases coordinate_154_15 (Fin.cases coordinate_154_16 (Fin.cases coordinate_154_17 (Fin.cases coordinate_154_18 (Fin.cases coordinate_154_19 (Fin.cases coordinate_154_20 (Fin.cases coordinate_154_21 (Fin.cases coordinate_154_22 (Fin.cases coordinate_154_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
