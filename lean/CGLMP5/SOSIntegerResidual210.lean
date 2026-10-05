import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear06
import CGLMP5.SOSPhaseLinear16

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_210_0 : commonDenominator 210 / (gramDenominator 10 * phaseDenominator 6) = 38406773954203744439537984551418143275722003324678171783580573456402815325440393493076432295528098750155855819126480156592917204980140335747835403697001009134632416289919402407591527569480081856647848576865262111260333357588232670135138041453095025046655632706407075624191644343144334280172655124947369617724072798898275949862785030161773062103786245886644017092478162582732449549475536294731073038116410016690025594459724334690197809292821000274947640456820556164108364421318005941878500948475 := by
  decide +kernel

private theorem scale_210_1 : commonDenominator 210 / (gramDenominator 35 * phaseDenominator 16) = 4607106699159127806861348734270062050410539120697327583901607524546005272316525344630640875371798621459505500924034994608982386192052693139282968624933209170995701798365448106058754849259272610414222498605126693024072661002164522832700388143053053532078638315418544484416733035399069568439211629582901410012417703264759797771986764466567167607689969782678030078464409182011657243190000070571188462284691274745846235747821733938463791330952372509741662443919873425687582124831921691850542467538736218243643692292716548 := by
  decide +kernel

private theorem scale_210_2 : commonDenominator 210 / (gramDenominator 45 * phaseDenominator 16) = 128764626991966545397860199165672809301840440519249531460423866138829326438623172341370492975076347325525022527844616795563221450821978793409197934760749141976669599135546630964251803137178691608773689099 := by
  decide +kernel

private theorem scale_210_3 : commonDenominator 210 / (gramDenominator 50 * phaseDenominator 16) = 19873027641108156235628523827941151986690204548205961820264814853062171492401145234363428583219830417892805251926081323516278188465570513183143202599917261981753872501621973125670344594706805 := by
  decide +kernel

private theorem scale_210_4 : commonDenominator 210 / (gramDenominator 120 * phaseDenominator 6) = 1939739431269314203615816394966379305331209297905819577572164869547461255467314428488118894243179778525033044413646985070078763238114552337597150341917706559455072208994824681821300674785998652213881830243201533731812248191738734891834529237683251841510833681710545023262283980804111298485700951968385243747114950 := by
  decide +kernel

private theorem scale_210_5 : commonDenominator 210 / (gramDenominator 134 * phaseDenominator 6) = 969869715634657101807908197483189652665604648952909788786082434773730627733657214244059447121589889262516522206823492535039381619057276168798575170958853279727536104497412340910650337392999326106940915121600766865906124095869367445917264618841625920755416840855272511631141990402055649242850475984192621873557475 := by
  decide +kernel

theorem denominator_divides_210 : ∀ f ∈ fiber 210, commonDenominator 210 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_210_0 : integerCoordinateClaim 210 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_0, phase_linear_16_0, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_1 : integerCoordinateClaim 210 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_1, phase_linear_16_1, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_2 : integerCoordinateClaim 210 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_2, phase_linear_16_2, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_3 : integerCoordinateClaim 210 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_3, phase_linear_16_3, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_4 : integerCoordinateClaim 210 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_4, phase_linear_16_4, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_5 : integerCoordinateClaim 210 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_5, phase_linear_16_5, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_6 : integerCoordinateClaim 210 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_6, phase_linear_16_6, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_7 : integerCoordinateClaim 210 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_7, phase_linear_16_7, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_8 : integerCoordinateClaim 210 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_8, phase_linear_16_8, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_9 : integerCoordinateClaim 210 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_9, phase_linear_16_9, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_10 : integerCoordinateClaim 210 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_10, phase_linear_16_10, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_11 : integerCoordinateClaim 210 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_11, phase_linear_16_11, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_12 : integerCoordinateClaim 210 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_12, phase_linear_16_12, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_13 : integerCoordinateClaim 210 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_13, phase_linear_16_13, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_14 : integerCoordinateClaim 210 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_14, phase_linear_16_14, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_15 : integerCoordinateClaim 210 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_15, phase_linear_16_15, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_16 : integerCoordinateClaim 210 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_16, phase_linear_16_16, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_17 : integerCoordinateClaim 210 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_17, phase_linear_16_17, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_18 : integerCoordinateClaim 210 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_18, phase_linear_16_18, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_19 : integerCoordinateClaim 210 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_19, phase_linear_16_19, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_20 : integerCoordinateClaim 210 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_20, phase_linear_16_20, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_21 : integerCoordinateClaim 210 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_21, phase_linear_16_21, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_22 : integerCoordinateClaim 210 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_22, phase_linear_16_22, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

private theorem coordinate_210_23 : integerCoordinateClaim 210 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_210]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_210_0, scale_210_1, scale_210_2, scale_210_3, scale_210_4, scale_210_5, phase_linear_6_23, phase_linear_16_23, gram_numerator_literal_10, gram_numerator_literal_35, gram_numerator_literal_45, gram_numerator_literal_50, gram_numerator_literal_120, gram_numerator_literal_134, denominator_literal_210, target_denominator_literal_210, target_numerator_literal_210]
  decide +kernel

theorem integer_residual_210 : integerResidualClaim 210 :=
  (Fin.cases coordinate_210_0 (Fin.cases coordinate_210_1 (Fin.cases coordinate_210_2 (Fin.cases coordinate_210_3 (Fin.cases coordinate_210_4 (Fin.cases coordinate_210_5 (Fin.cases coordinate_210_6 (Fin.cases coordinate_210_7 (Fin.cases coordinate_210_8 (Fin.cases coordinate_210_9 (Fin.cases coordinate_210_10 (Fin.cases coordinate_210_11 (Fin.cases coordinate_210_12 (Fin.cases coordinate_210_13 (Fin.cases coordinate_210_14 (Fin.cases coordinate_210_15 (Fin.cases coordinate_210_16 (Fin.cases coordinate_210_17 (Fin.cases coordinate_210_18 (Fin.cases coordinate_210_19 (Fin.cases coordinate_210_20 (Fin.cases coordinate_210_21 (Fin.cases coordinate_210_22 (Fin.cases coordinate_210_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
