import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear02
import CGLMP5.SOSPhaseLinear12

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_54_0 : commonDenominator 54 / (gramDenominator 70 * phaseDenominator 2) = 20168612178160591503622412459701413249235583654793385708871187565420158508603899971842773799047732360121871933332826099378252920755015732031509332770631370543125727481413362018065413787357355034132725995629282485429553910040653411995271684107014526066812384991869316921569517586709620287537924426998402821481139668784901900683270613324100609915794594662181107203401 := by
  decide +kernel

private theorem scale_54_1 : commonDenominator 54 / (gramDenominator 79 * phaseDenominator 2) = 1 := by
  decide +kernel

private theorem scale_54_2 : commonDenominator 54 / (gramDenominator 80 * phaseDenominator 2) = 14649617754197345294212900979967141924082563095060536037221768139338659885076831831658709083160213242469337329085236963558381451588657897435113923893055055650108938916051675242472155320 := by
  decide +kernel

private theorem scale_54_3 : commonDenominator 54 / (gramDenominator 84 * phaseDenominator 12) = 7835837121786961380964683913627093204210099824364885721087283045422181609613263950207761871369300866865526898675628914940877461871953853025262961779357918110270217067176352366101723002825844521473331356301994812634206644215071984787831637361303124922188441583014163876672146679070850768023042105267069226449185241251002125320794092973702567739774999825235357661388977689509881003275661280193056876084182196781047069147280476329623776644007611045723900754660281897263674077362012446620945278199739070792213757497538555163472004524168431468451577814582390845284338377175000746542555715386324466220500724575270169280293712812000 := by
  decide +kernel

theorem denominator_divides_054 : ∀ f ∈ fiber 54, commonDenominator 54 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_54_0 : integerCoordinateClaim 54 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_0, phase_linear_12_0, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_1 : integerCoordinateClaim 54 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_1, phase_linear_12_1, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_2 : integerCoordinateClaim 54 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_2, phase_linear_12_2, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_3 : integerCoordinateClaim 54 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_3, phase_linear_12_3, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_4 : integerCoordinateClaim 54 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_4, phase_linear_12_4, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_5 : integerCoordinateClaim 54 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_5, phase_linear_12_5, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_6 : integerCoordinateClaim 54 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_6, phase_linear_12_6, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_7 : integerCoordinateClaim 54 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_7, phase_linear_12_7, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_8 : integerCoordinateClaim 54 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_8, phase_linear_12_8, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_9 : integerCoordinateClaim 54 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_9, phase_linear_12_9, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_10 : integerCoordinateClaim 54 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_10, phase_linear_12_10, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_11 : integerCoordinateClaim 54 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_11, phase_linear_12_11, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_12 : integerCoordinateClaim 54 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_12, phase_linear_12_12, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_13 : integerCoordinateClaim 54 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_13, phase_linear_12_13, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_14 : integerCoordinateClaim 54 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_14, phase_linear_12_14, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_15 : integerCoordinateClaim 54 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_15, phase_linear_12_15, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_16 : integerCoordinateClaim 54 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_16, phase_linear_12_16, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_17 : integerCoordinateClaim 54 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_17, phase_linear_12_17, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_18 : integerCoordinateClaim 54 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_18, phase_linear_12_18, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_19 : integerCoordinateClaim 54 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_19, phase_linear_12_19, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_20 : integerCoordinateClaim 54 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_20, phase_linear_12_20, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_21 : integerCoordinateClaim 54 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_21, phase_linear_12_21, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_22 : integerCoordinateClaim 54 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_22, phase_linear_12_22, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

private theorem coordinate_54_23 : integerCoordinateClaim 54 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_54]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_54_0, scale_54_1, scale_54_2, scale_54_3, phase_linear_2_23, phase_linear_12_23, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_54, target_denominator_literal_54, target_numerator_literal_54]
  decide +kernel

theorem integer_residual_054 : integerResidualClaim 54 :=
  (Fin.cases coordinate_54_0 (Fin.cases coordinate_54_1 (Fin.cases coordinate_54_2 (Fin.cases coordinate_54_3 (Fin.cases coordinate_54_4 (Fin.cases coordinate_54_5 (Fin.cases coordinate_54_6 (Fin.cases coordinate_54_7 (Fin.cases coordinate_54_8 (Fin.cases coordinate_54_9 (Fin.cases coordinate_54_10 (Fin.cases coordinate_54_11 (Fin.cases coordinate_54_12 (Fin.cases coordinate_54_13 (Fin.cases coordinate_54_14 (Fin.cases coordinate_54_15 (Fin.cases coordinate_54_16 (Fin.cases coordinate_54_17 (Fin.cases coordinate_54_18 (Fin.cases coordinate_54_19 (Fin.cases coordinate_54_20 (Fin.cases coordinate_54_21 (Fin.cases coordinate_54_22 (Fin.cases coordinate_54_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
