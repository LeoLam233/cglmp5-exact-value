import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear14
import CGLMP5.SOSPhaseLinear19

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_87_0 : commonDenominator 87 / (gramDenominator 11 * phaseDenominator 19) = 2362303436024831191292969575489110849898833974934561978410086535948080216576439044247825372052047273289195908517170282806143302294457738369580764227408815255061863460970885387150199924817250846162693365934802728572047586163010186963486546611345474859932898296527602063268556049726134389598750353154868225053042208644172955141184891433163623064505444943972887645896833659028963920473481999686976556933270363161176192232929974099087799135334293052821917855631887832425185605 := by
  decide +kernel

private theorem scale_87_1 : commonDenominator 87 / (gramDenominator 36 * phaseDenominator 14) = 4607106699159127806861348734270062050410539120697327583901607524546005272316525344630640875371798621459505500924034994608982386192052693139282968624933209170995701798365448106058754849259272610414222498605126693024072661002164522832700388143053053532078638315418544484416733035399069568439211629582901410012417703264759797771986764466567167607689969782678030078464409182011657243190000070571188462284691274745846235747821733938463791330952372509741662443919873425687582124831921691850542467538736218243643692292716548 := by
  decide +kernel

private theorem scale_87_2 : commonDenominator 87 / (gramDenominator 46 * phaseDenominator 14) = 79199862280618519798273268966545365881205511045012640188636787778976385318017244126454655389943874873847973247939695338867737414126780092921890106687092609327670293347333299155464722 := by
  decide +kernel

private theorem scale_87_3 : commonDenominator 87 / (gramDenominator 51 * phaseDenominator 14) = 7949211056443262494251409531176460794676081819282384728105925941224868596960458093745371433287932167157122100770432529406511275386228205273257281039966904792701549000648789250268137837882722 := by
  decide +kernel

private theorem scale_87_4 : commonDenominator 87 / (gramDenominator 124 * phaseDenominator 14) = 59654230903957640817769819277896287578604635305525125408460348247878310879294073301919235829211405665347292463138348954342992008558554988309086468828611807460880367224940016403884022569097634541670308101159429483386188413747803166714371984886194773728775140015112988577591279707152038035805 := by
  decide +kernel

private theorem scale_87_5 : commonDenominator 87 / (gramDenominator 128 * phaseDenominator 14) = 59654230903957640817769819277896287578604635305525125408460348247878310879294073301919235829211405665347292463138348954342992008558554988309086468828611807460880367224940016403884022569097634541670308101159429483386188413747803166714371984886194773728775140015112988577591279707152038035805 := by
  decide +kernel

theorem denominator_divides_087 : ∀ f ∈ fiber 87, commonDenominator 87 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_87_0 : integerCoordinateClaim 87 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_0, phase_linear_19_0, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_1 : integerCoordinateClaim 87 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_1, phase_linear_19_1, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_2 : integerCoordinateClaim 87 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_2, phase_linear_19_2, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_3 : integerCoordinateClaim 87 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_3, phase_linear_19_3, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_4 : integerCoordinateClaim 87 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_4, phase_linear_19_4, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_5 : integerCoordinateClaim 87 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_5, phase_linear_19_5, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_6 : integerCoordinateClaim 87 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_6, phase_linear_19_6, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_7 : integerCoordinateClaim 87 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_7, phase_linear_19_7, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_8 : integerCoordinateClaim 87 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_8, phase_linear_19_8, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_9 : integerCoordinateClaim 87 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_9, phase_linear_19_9, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_10 : integerCoordinateClaim 87 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_10, phase_linear_19_10, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_11 : integerCoordinateClaim 87 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_11, phase_linear_19_11, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_12 : integerCoordinateClaim 87 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_12, phase_linear_19_12, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_13 : integerCoordinateClaim 87 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_13, phase_linear_19_13, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_14 : integerCoordinateClaim 87 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_14, phase_linear_19_14, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_15 : integerCoordinateClaim 87 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_15, phase_linear_19_15, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_16 : integerCoordinateClaim 87 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_16, phase_linear_19_16, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_17 : integerCoordinateClaim 87 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_17, phase_linear_19_17, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_18 : integerCoordinateClaim 87 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_18, phase_linear_19_18, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_19 : integerCoordinateClaim 87 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_19, phase_linear_19_19, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_20 : integerCoordinateClaim 87 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_20, phase_linear_19_20, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_21 : integerCoordinateClaim 87 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_21, phase_linear_19_21, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_22 : integerCoordinateClaim 87 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_22, phase_linear_19_22, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

private theorem coordinate_87_23 : integerCoordinateClaim 87 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_87]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_87_0, scale_87_1, scale_87_2, scale_87_3, scale_87_4, scale_87_5, phase_linear_14_23, phase_linear_19_23, gram_numerator_literal_11, gram_numerator_literal_36, gram_numerator_literal_46, gram_numerator_literal_51, gram_numerator_literal_124, gram_numerator_literal_128, denominator_literal_87, target_denominator_literal_87, target_numerator_literal_87]
  decide +kernel

theorem integer_residual_087 : integerResidualClaim 87 :=
  (Fin.cases coordinate_87_0 (Fin.cases coordinate_87_1 (Fin.cases coordinate_87_2 (Fin.cases coordinate_87_3 (Fin.cases coordinate_87_4 (Fin.cases coordinate_87_5 (Fin.cases coordinate_87_6 (Fin.cases coordinate_87_7 (Fin.cases coordinate_87_8 (Fin.cases coordinate_87_9 (Fin.cases coordinate_87_10 (Fin.cases coordinate_87_11 (Fin.cases coordinate_87_12 (Fin.cases coordinate_87_13 (Fin.cases coordinate_87_14 (Fin.cases coordinate_87_15 (Fin.cases coordinate_87_16 (Fin.cases coordinate_87_17 (Fin.cases coordinate_87_18 (Fin.cases coordinate_87_19 (Fin.cases coordinate_87_20 (Fin.cases coordinate_87_21 (Fin.cases coordinate_87_22 (Fin.cases coordinate_87_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
