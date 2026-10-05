import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear05
import CGLMP5.SOSPhaseLinear10

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_48_0 : commonDenominator 48 / (gramDenominator 14 * phaseDenominator 5) = 2362303436024831191292969575489110849898833974934561978410086535948080216576439044247825372052047273289195908517170282806143302294457738369580764227408815255061863460970885387150199924817250846162693365934802728572047586163010186963486546611345474859932898296527602063268556049726134389598750353154868225053042208644172955141184891433163623064505444943972887645896833659028963920473481999686976556933270363161176192232929974099087799135334293052821917855631887832425185605 := by
  decide +kernel

private theorem scale_48_1 : commonDenominator 48 / (gramDenominator 39 * phaseDenominator 10) = 4607106699159127806861348734270062050410539120697327583901607524546005272316525344630640875371798621459505500924034994608982386192052693139282968624933209170995701798365448106058754849259272610414222498605126693024072661002164522832700388143053053532078638315418544484416733035399069568439211629582901410012417703264759797771986764466567167607689969782678030078464409182011657243190000070571188462284691274745846235747821733938463791330952372509741662443919873425687582124831921691850542467538736218243643692292716548 := by
  decide +kernel

private theorem scale_48_2 : commonDenominator 48 / (gramDenominator 48 * phaseDenominator 10) = 79199862280618519798273268966545365881205511045012640188636787778976385318017244126454655389943874873847973247939695338867737414126780092921890106687092609327670293347333299155464722 := by
  decide +kernel

private theorem scale_48_3 : commonDenominator 48 / (gramDenominator 52 * phaseDenominator 10) = 7949211056443262494251409531176460794676081819282384728105925941224868596960458093745371433287932167157122100770432529406511275386228205273257281039966904792701549000648789250268137837882722 := by
  decide +kernel

private theorem scale_48_4 : commonDenominator 48 / (gramDenominator 121 * phaseDenominator 10) = 59654230903957640817769819277896287578604635305525125408460348247878310879294073301919235829211405665347292463138348954342992008558554988309086468828611807460880367224940016403884022569097634541670308101159429483386188413747803166714371984886194773728775140015112988577591279707152038035805 := by
  decide +kernel

private theorem scale_48_5 : commonDenominator 48 / (gramDenominator 132 * phaseDenominator 10) = 59654230903957640817769819277896287578604635305525125408460348247878310879294073301919235829211405665347292463138348954342992008558554988309086468828611807460880367224940016403884022569097634541670308101159429483386188413747803166714371984886194773728775140015112988577591279707152038035805 := by
  decide +kernel

theorem denominator_divides_048 : ∀ f ∈ fiber 48, commonDenominator 48 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_48_0 : integerCoordinateClaim 48 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_0, phase_linear_10_0, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_1 : integerCoordinateClaim 48 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_1, phase_linear_10_1, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_2 : integerCoordinateClaim 48 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_2, phase_linear_10_2, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_3 : integerCoordinateClaim 48 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_3, phase_linear_10_3, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_4 : integerCoordinateClaim 48 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_4, phase_linear_10_4, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_5 : integerCoordinateClaim 48 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_5, phase_linear_10_5, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_6 : integerCoordinateClaim 48 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_6, phase_linear_10_6, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_7 : integerCoordinateClaim 48 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_7, phase_linear_10_7, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_8 : integerCoordinateClaim 48 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_8, phase_linear_10_8, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_9 : integerCoordinateClaim 48 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_9, phase_linear_10_9, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_10 : integerCoordinateClaim 48 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_10, phase_linear_10_10, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_11 : integerCoordinateClaim 48 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_11, phase_linear_10_11, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_12 : integerCoordinateClaim 48 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_12, phase_linear_10_12, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_13 : integerCoordinateClaim 48 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_13, phase_linear_10_13, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_14 : integerCoordinateClaim 48 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_14, phase_linear_10_14, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_15 : integerCoordinateClaim 48 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_15, phase_linear_10_15, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_16 : integerCoordinateClaim 48 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_16, phase_linear_10_16, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_17 : integerCoordinateClaim 48 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_17, phase_linear_10_17, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_18 : integerCoordinateClaim 48 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_18, phase_linear_10_18, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_19 : integerCoordinateClaim 48 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_19, phase_linear_10_19, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_20 : integerCoordinateClaim 48 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_20, phase_linear_10_20, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_21 : integerCoordinateClaim 48 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_21, phase_linear_10_21, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_22 : integerCoordinateClaim 48 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_22, phase_linear_10_22, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

private theorem coordinate_48_23 : integerCoordinateClaim 48 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_48]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_48_0, scale_48_1, scale_48_2, scale_48_3, scale_48_4, scale_48_5, phase_linear_5_23, phase_linear_10_23, gram_numerator_literal_14, gram_numerator_literal_39, gram_numerator_literal_48, gram_numerator_literal_52, gram_numerator_literal_121, gram_numerator_literal_132, denominator_literal_48, target_denominator_literal_48, target_numerator_literal_48]
  decide +kernel

theorem integer_residual_048 : integerResidualClaim 48 :=
  (Fin.cases coordinate_48_0 (Fin.cases coordinate_48_1 (Fin.cases coordinate_48_2 (Fin.cases coordinate_48_3 (Fin.cases coordinate_48_4 (Fin.cases coordinate_48_5 (Fin.cases coordinate_48_6 (Fin.cases coordinate_48_7 (Fin.cases coordinate_48_8 (Fin.cases coordinate_48_9 (Fin.cases coordinate_48_10 (Fin.cases coordinate_48_11 (Fin.cases coordinate_48_12 (Fin.cases coordinate_48_13 (Fin.cases coordinate_48_14 (Fin.cases coordinate_48_15 (Fin.cases coordinate_48_16 (Fin.cases coordinate_48_17 (Fin.cases coordinate_48_18 (Fin.cases coordinate_48_19 (Fin.cases coordinate_48_20 (Fin.cases coordinate_48_21 (Fin.cases coordinate_48_22 (Fin.cases coordinate_48_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
