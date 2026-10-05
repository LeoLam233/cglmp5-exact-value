import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear02
import CGLMP5.SOSPhaseLinear12

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_161_0 : commonDenominator 161 / (gramDenominator 10 * phaseDenominator 2) = 38406773954203744439537984551418143275722003324678171783580573456402815325440393493076432295528098750155855819126480156592917204980140335747835403697001009134632416289919402407591527569480081856647848576865262111260333357588232670135138041453095025046655632706407075624191644343144334280172655124947369617724072798898275949862785030161773062103786245886644017092478162582732449549475536294731073038116410016690025594459724334690197809292821000274947640456820556164108364421318005941878500948475 := by
  decide +kernel

private theorem scale_161_1 : commonDenominator 161 / (gramDenominator 35 * phaseDenominator 12) = 4607106699159127806861348734270062050410539120697327583901607524546005272316525344630640875371798621459505500924034994608982386192052693139282968624933209170995701798365448106058754849259272610414222498605126693024072661002164522832700388143053053532078638315418544484416733035399069568439211629582901410012417703264759797771986764466567167607689969782678030078464409182011657243190000070571188462284691274745846235747821733938463791330952372509741662443919873425687582124831921691850542467538736218243643692292716548 := by
  decide +kernel

private theorem scale_161_2 : commonDenominator 161 / (gramDenominator 45 * phaseDenominator 12) = 128764626991966545397860199165672809301840440519249531460423866138829326438623172341370492975076347325525022527844616795563221450821978793409197934760749141976669599135546630964251803137178691608773689099 := by
  decide +kernel

private theorem scale_161_3 : commonDenominator 161 / (gramDenominator 50 * phaseDenominator 12) = 19873027641108156235628523827941151986690204548205961820264814853062171492401145234363428583219830417892805251926081323516278188465570513183143202599917261981753872501621973125670344594706805 := by
  decide +kernel

private theorem scale_161_4 : commonDenominator 161 / (gramDenominator 120 * phaseDenominator 2) = 1939739431269314203615816394966379305331209297905819577572164869547461255467314428488118894243179778525033044413646985070078763238114552337597150341917706559455072208994824681821300674785998652213881830243201533731812248191738734891834529237683251841510833681710545023262283980804111298485700951968385243747114950 := by
  decide +kernel

private theorem scale_161_5 : commonDenominator 161 / (gramDenominator 134 * phaseDenominator 2) = 969869715634657101807908197483189652665604648952909788786082434773730627733657214244059447121589889262516522206823492535039381619057276168798575170958853279727536104497412340910650337392999326106940915121600766865906124095869367445917264618841625920755416840855272511631141990402055649242850475984192621873557475 := by
  decide +kernel

theorem denominator_divides_161 : ∀ f ∈ fiber 161, commonDenominator 161 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_161_0 : integerCoordinateClaim 161 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_0, phase_linear_12_0, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_1 : integerCoordinateClaim 161 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_1, phase_linear_12_1, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_2 : integerCoordinateClaim 161 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_2, phase_linear_12_2, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_3 : integerCoordinateClaim 161 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_3, phase_linear_12_3, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_4 : integerCoordinateClaim 161 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_4, phase_linear_12_4, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_5 : integerCoordinateClaim 161 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_5, phase_linear_12_5, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_6 : integerCoordinateClaim 161 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_6, phase_linear_12_6, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_7 : integerCoordinateClaim 161 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_7, phase_linear_12_7, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_8 : integerCoordinateClaim 161 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_8, phase_linear_12_8, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_9 : integerCoordinateClaim 161 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_9, phase_linear_12_9, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_10 : integerCoordinateClaim 161 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_10, phase_linear_12_10, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_11 : integerCoordinateClaim 161 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_11, phase_linear_12_11, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_12 : integerCoordinateClaim 161 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_12, phase_linear_12_12, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_13 : integerCoordinateClaim 161 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_13, phase_linear_12_13, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_14 : integerCoordinateClaim 161 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_14, phase_linear_12_14, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_15 : integerCoordinateClaim 161 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_15, phase_linear_12_15, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_16 : integerCoordinateClaim 161 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_16, phase_linear_12_16, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_17 : integerCoordinateClaim 161 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_17, phase_linear_12_17, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_18 : integerCoordinateClaim 161 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_18, phase_linear_12_18, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_19 : integerCoordinateClaim 161 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_19, phase_linear_12_19, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_20 : integerCoordinateClaim 161 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_20, phase_linear_12_20, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_21 : integerCoordinateClaim 161 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_21, phase_linear_12_21, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_22 : integerCoordinateClaim 161 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_22, phase_linear_12_22, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

private theorem coordinate_161_23 : integerCoordinateClaim 161 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_161]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_161_0, scale_161_1, scale_161_2, scale_161_3, scale_161_4, scale_161_5, phase_linear_2_23, phase_linear_12_23, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_161, target_denominator_literal_161, target_numerator_literal_161]
  decide +kernel

theorem integer_residual_161 : integerResidualClaim 161 :=
  (Fin.cases coordinate_161_0 (Fin.cases coordinate_161_1 (Fin.cases coordinate_161_2 (Fin.cases coordinate_161_3 (Fin.cases coordinate_161_4 (Fin.cases coordinate_161_5 (Fin.cases coordinate_161_6 (Fin.cases coordinate_161_7 (Fin.cases coordinate_161_8 (Fin.cases coordinate_161_9 (Fin.cases coordinate_161_10 (Fin.cases coordinate_161_11 (Fin.cases coordinate_161_12 (Fin.cases coordinate_161_13 (Fin.cases coordinate_161_14 (Fin.cases coordinate_161_15 (Fin.cases coordinate_161_16 (Fin.cases coordinate_161_17 (Fin.cases coordinate_161_18 (Fin.cases coordinate_161_19 (Fin.cases coordinate_161_20 (Fin.cases coordinate_161_21 (Fin.cases coordinate_161_22 (Fin.cases coordinate_161_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
