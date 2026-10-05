import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear08
import CGLMP5.SOSPhaseLinear18

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_240_0 : commonDenominator 240 / (gramDenominator 10 * phaseDenominator 18) = 38406773954203744439537984551418143275722003324678171783580573456402815325440393493076432295528098750155855819126480156592917204980140335747835403697001009134632416289919402407591527569480081856647848576865262111260333357588232670135138041453095025046655632706407075624191644343144334280172655124947369617724072798898275949862785030161773062103786245886644017092478162582732449549475536294731073038116410016690025594459724334690197809292821000274947640456820556164108364421318005941878500948475 := by
  decide +kernel

private theorem scale_240_1 : commonDenominator 240 / (gramDenominator 35 * phaseDenominator 8) = 4607106699159127806861348734270062050410539120697327583901607524546005272316525344630640875371798621459505500924034994608982386192052693139282968624933209170995701798365448106058754849259272610414222498605126693024072661002164522832700388143053053532078638315418544484416733035399069568439211629582901410012417703264759797771986764466567167607689969782678030078464409182011657243190000070571188462284691274745846235747821733938463791330952372509741662443919873425687582124831921691850542467538736218243643692292716548 := by
  decide +kernel

private theorem scale_240_2 : commonDenominator 240 / (gramDenominator 45 * phaseDenominator 8) = 128764626991966545397860199165672809301840440519249531460423866138829326438623172341370492975076347325525022527844616795563221450821978793409197934760749141976669599135546630964251803137178691608773689099 := by
  decide +kernel

private theorem scale_240_3 : commonDenominator 240 / (gramDenominator 50 * phaseDenominator 8) = 19873027641108156235628523827941151986690204548205961820264814853062171492401145234363428583219830417892805251926081323516278188465570513183143202599917261981753872501621973125670344594706805 := by
  decide +kernel

private theorem scale_240_4 : commonDenominator 240 / (gramDenominator 120 * phaseDenominator 18) = 1939739431269314203615816394966379305331209297905819577572164869547461255467314428488118894243179778525033044413646985070078763238114552337597150341917706559455072208994824681821300674785998652213881830243201533731812248191738734891834529237683251841510833681710545023262283980804111298485700951968385243747114950 := by
  decide +kernel

private theorem scale_240_5 : commonDenominator 240 / (gramDenominator 134 * phaseDenominator 18) = 969869715634657101807908197483189652665604648952909788786082434773730627733657214244059447121589889262516522206823492535039381619057276168798575170958853279727536104497412340910650337392999326106940915121600766865906124095869367445917264618841625920755416840855272511631141990402055649242850475984192621873557475 := by
  decide +kernel

theorem denominator_divides_240 : ∀ f ∈ fiber 240, commonDenominator 240 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_240_0 : integerCoordinateClaim 240 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_0, phase_linear_18_0, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_1 : integerCoordinateClaim 240 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_1, phase_linear_18_1, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_2 : integerCoordinateClaim 240 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_2, phase_linear_18_2, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_3 : integerCoordinateClaim 240 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_3, phase_linear_18_3, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_4 : integerCoordinateClaim 240 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_4, phase_linear_18_4, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_5 : integerCoordinateClaim 240 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_5, phase_linear_18_5, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_6 : integerCoordinateClaim 240 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_6, phase_linear_18_6, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_7 : integerCoordinateClaim 240 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_7, phase_linear_18_7, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_8 : integerCoordinateClaim 240 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_8, phase_linear_18_8, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_9 : integerCoordinateClaim 240 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_9, phase_linear_18_9, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_10 : integerCoordinateClaim 240 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_10, phase_linear_18_10, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_11 : integerCoordinateClaim 240 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_11, phase_linear_18_11, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_12 : integerCoordinateClaim 240 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_12, phase_linear_18_12, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_13 : integerCoordinateClaim 240 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_13, phase_linear_18_13, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_14 : integerCoordinateClaim 240 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_14, phase_linear_18_14, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_15 : integerCoordinateClaim 240 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_15, phase_linear_18_15, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_16 : integerCoordinateClaim 240 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_16, phase_linear_18_16, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_17 : integerCoordinateClaim 240 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_17, phase_linear_18_17, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_18 : integerCoordinateClaim 240 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_18, phase_linear_18_18, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_19 : integerCoordinateClaim 240 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_19, phase_linear_18_19, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_20 : integerCoordinateClaim 240 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_20, phase_linear_18_20, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_21 : integerCoordinateClaim 240 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_21, phase_linear_18_21, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_22 : integerCoordinateClaim 240 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_22, phase_linear_18_22, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

private theorem coordinate_240_23 : integerCoordinateClaim 240 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_240]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_240_0, scale_240_1, scale_240_2, scale_240_3, scale_240_4, scale_240_5, phase_linear_8_23, phase_linear_18_23, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_240, target_denominator_literal_240, target_numerator_literal_240]
  decide +kernel

theorem integer_residual_240 : integerResidualClaim 240 :=
  (Fin.cases coordinate_240_0 (Fin.cases coordinate_240_1 (Fin.cases coordinate_240_2 (Fin.cases coordinate_240_3 (Fin.cases coordinate_240_4 (Fin.cases coordinate_240_5 (Fin.cases coordinate_240_6 (Fin.cases coordinate_240_7 (Fin.cases coordinate_240_8 (Fin.cases coordinate_240_9 (Fin.cases coordinate_240_10 (Fin.cases coordinate_240_11 (Fin.cases coordinate_240_12 (Fin.cases coordinate_240_13 (Fin.cases coordinate_240_14 (Fin.cases coordinate_240_15 (Fin.cases coordinate_240_16 (Fin.cases coordinate_240_17 (Fin.cases coordinate_240_18 (Fin.cases coordinate_240_19 (Fin.cases coordinate_240_20 (Fin.cases coordinate_240_21 (Fin.cases coordinate_240_22 (Fin.cases coordinate_240_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
