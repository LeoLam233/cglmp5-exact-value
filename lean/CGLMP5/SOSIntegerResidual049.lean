import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear01
import CGLMP5.SOSPhaseLinear06

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_49_0 : commonDenominator 49 / (gramDenominator 14 * phaseDenominator 1) = 2362303436024831191292969575489110849898833974934561978410086535948080216576439044247825372052047273289195908517170282806143302294457738369580764227408815255061863460970885387150199924817250846162693365934802728572047586163010186963486546611345474859932898296527602063268556049726134389598750353154868225053042208644172955141184891433163623064505444943972887645896833659028963920473481999686976556933270363161176192232929974099087799135334293052821917855631887832425185605 := by
  decide +kernel

private theorem scale_49_1 : commonDenominator 49 / (gramDenominator 39 * phaseDenominator 6) = 4607106699159127806861348734270062050410539120697327583901607524546005272316525344630640875371798621459505500924034994608982386192052693139282968624933209170995701798365448106058754849259272610414222498605126693024072661002164522832700388143053053532078638315418544484416733035399069568439211629582901410012417703264759797771986764466567167607689969782678030078464409182011657243190000070571188462284691274745846235747821733938463791330952372509741662443919873425687582124831921691850542467538736218243643692292716548 := by
  decide +kernel

private theorem scale_49_2 : commonDenominator 49 / (gramDenominator 48 * phaseDenominator 6) = 79199862280618519798273268966545365881205511045012640188636787778976385318017244126454655389943874873847973247939695338867737414126780092921890106687092609327670293347333299155464722 := by
  decide +kernel

private theorem scale_49_3 : commonDenominator 49 / (gramDenominator 52 * phaseDenominator 6) = 7949211056443262494251409531176460794676081819282384728105925941224868596960458093745371433287932167157122100770432529406511275386228205273257281039966904792701549000648789250268137837882722 := by
  decide +kernel

private theorem scale_49_4 : commonDenominator 49 / (gramDenominator 121 * phaseDenominator 6) = 59654230903957640817769819277896287578604635305525125408460348247878310879294073301919235829211405665347292463138348954342992008558554988309086468828611807460880367224940016403884022569097634541670308101159429483386188413747803166714371984886194773728775140015112988577591279707152038035805 := by
  decide +kernel

private theorem scale_49_5 : commonDenominator 49 / (gramDenominator 132 * phaseDenominator 6) = 59654230903957640817769819277896287578604635305525125408460348247878310879294073301919235829211405665347292463138348954342992008558554988309086468828611807460880367224940016403884022569097634541670308101159429483386188413747803166714371984886194773728775140015112988577591279707152038035805 := by
  decide +kernel

theorem denominator_divides_049 : ∀ f ∈ fiber 49, commonDenominator 49 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_49_0 : integerCoordinateClaim 49 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_0, phase_linear_6_0, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_1 : integerCoordinateClaim 49 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_1, phase_linear_6_1, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_2 : integerCoordinateClaim 49 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_2, phase_linear_6_2, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_3 : integerCoordinateClaim 49 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_3, phase_linear_6_3, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_4 : integerCoordinateClaim 49 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_4, phase_linear_6_4, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_5 : integerCoordinateClaim 49 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_5, phase_linear_6_5, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_6 : integerCoordinateClaim 49 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_6, phase_linear_6_6, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_7 : integerCoordinateClaim 49 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_7, phase_linear_6_7, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_8 : integerCoordinateClaim 49 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_8, phase_linear_6_8, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_9 : integerCoordinateClaim 49 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_9, phase_linear_6_9, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_10 : integerCoordinateClaim 49 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_10, phase_linear_6_10, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_11 : integerCoordinateClaim 49 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_11, phase_linear_6_11, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_12 : integerCoordinateClaim 49 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_12, phase_linear_6_12, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_13 : integerCoordinateClaim 49 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_13, phase_linear_6_13, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_14 : integerCoordinateClaim 49 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_14, phase_linear_6_14, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_15 : integerCoordinateClaim 49 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_15, phase_linear_6_15, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_16 : integerCoordinateClaim 49 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_16, phase_linear_6_16, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_17 : integerCoordinateClaim 49 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_17, phase_linear_6_17, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_18 : integerCoordinateClaim 49 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_18, phase_linear_6_18, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_19 : integerCoordinateClaim 49 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_19, phase_linear_6_19, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_20 : integerCoordinateClaim 49 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_20, phase_linear_6_20, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_21 : integerCoordinateClaim 49 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_21, phase_linear_6_21, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_22 : integerCoordinateClaim 49 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_22, phase_linear_6_22, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

private theorem coordinate_49_23 : integerCoordinateClaim 49 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_49]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_49_0, scale_49_1, scale_49_2, scale_49_3, scale_49_4, scale_49_5, phase_linear_1_23, phase_linear_6_23, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_49, target_denominator_literal_49, target_numerator_literal_49]
  decide +kernel

theorem integer_residual_049 : integerResidualClaim 49 :=
  (Fin.cases coordinate_49_0 (Fin.cases coordinate_49_1 (Fin.cases coordinate_49_2 (Fin.cases coordinate_49_3 (Fin.cases coordinate_49_4 (Fin.cases coordinate_49_5 (Fin.cases coordinate_49_6 (Fin.cases coordinate_49_7 (Fin.cases coordinate_49_8 (Fin.cases coordinate_49_9 (Fin.cases coordinate_49_10 (Fin.cases coordinate_49_11 (Fin.cases coordinate_49_12 (Fin.cases coordinate_49_13 (Fin.cases coordinate_49_14 (Fin.cases coordinate_49_15 (Fin.cases coordinate_49_16 (Fin.cases coordinate_49_17 (Fin.cases coordinate_49_18 (Fin.cases coordinate_49_19 (Fin.cases coordinate_49_20 (Fin.cases coordinate_49_21 (Fin.cases coordinate_49_22 (Fin.cases coordinate_49_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
