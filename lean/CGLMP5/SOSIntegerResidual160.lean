import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear04
import CGLMP5.SOSPhaseLinear14

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_160_0 : commonDenominator 160 / (gramDenominator 70 * phaseDenominator 14) = 20168612178160591503622412459701413249235583654793385708871187565420158508603899971842773799047732360121871933332826099378252920755015732031509332770631370543125727481413362018065413787357355034132725995629282485429553910040653411995271684107014526066812384991869316921569517586709620287537924426998402821481139668784901900683270613324100609915794594662181107203401 := by
  decide +kernel

private theorem scale_160_1 : commonDenominator 160 / (gramDenominator 79 * phaseDenominator 14) = 1 := by
  decide +kernel

private theorem scale_160_2 : commonDenominator 160 / (gramDenominator 80 * phaseDenominator 14) = 14649617754197345294212900979967141924082563095060536037221768139338659885076831831658709083160213242469337329085236963558381451588657897435113923893055055650108938916051675242472155320 := by
  decide +kernel

private theorem scale_160_3 : commonDenominator 160 / (gramDenominator 84 * phaseDenominator 4) = 7835837121786961380964683913627093204210099824364885721087283045422181609613263950207761871369300866865526898675628914940877461871953853025262961779357918110270217067176352366101723002825844521473331356301994812634206644215071984787831637361303124922188441583014163876672146679070850768023042105267069226449185241251002125320794092973702567739774999825235357661388977689509881003275661280193056876084182196781047069147280476329623776644007611045723900754660281897263674077362012446620945278199739070792213757497538555163472004524168431468451577814582390845284338377175000746542555715386324466220500724575270169280293712812000 := by
  decide +kernel

theorem denominator_divides_160 : ∀ f ∈ fiber 160, commonDenominator 160 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_160_0 : integerCoordinateClaim 160 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_0, phase_linear_14_0, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_1 : integerCoordinateClaim 160 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_1, phase_linear_14_1, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_2 : integerCoordinateClaim 160 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_2, phase_linear_14_2, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_3 : integerCoordinateClaim 160 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_3, phase_linear_14_3, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_4 : integerCoordinateClaim 160 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_4, phase_linear_14_4, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_5 : integerCoordinateClaim 160 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_5, phase_linear_14_5, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_6 : integerCoordinateClaim 160 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_6, phase_linear_14_6, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_7 : integerCoordinateClaim 160 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_7, phase_linear_14_7, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_8 : integerCoordinateClaim 160 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_8, phase_linear_14_8, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_9 : integerCoordinateClaim 160 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_9, phase_linear_14_9, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_10 : integerCoordinateClaim 160 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_10, phase_linear_14_10, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_11 : integerCoordinateClaim 160 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_11, phase_linear_14_11, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_12 : integerCoordinateClaim 160 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_12, phase_linear_14_12, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_13 : integerCoordinateClaim 160 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_13, phase_linear_14_13, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_14 : integerCoordinateClaim 160 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_14, phase_linear_14_14, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_15 : integerCoordinateClaim 160 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_15, phase_linear_14_15, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_16 : integerCoordinateClaim 160 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_16, phase_linear_14_16, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_17 : integerCoordinateClaim 160 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_17, phase_linear_14_17, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_18 : integerCoordinateClaim 160 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_18, phase_linear_14_18, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_19 : integerCoordinateClaim 160 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_19, phase_linear_14_19, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_20 : integerCoordinateClaim 160 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_20, phase_linear_14_20, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_21 : integerCoordinateClaim 160 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_21, phase_linear_14_21, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_22 : integerCoordinateClaim 160 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_22, phase_linear_14_22, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

private theorem coordinate_160_23 : integerCoordinateClaim 160 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_160]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_160_0, scale_160_1, scale_160_2, scale_160_3, phase_linear_4_23, phase_linear_14_23, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_160, target_denominator_literal_160, target_numerator_literal_160]
  decide +kernel

theorem integer_residual_160 : integerResidualClaim 160 :=
  (Fin.cases coordinate_160_0 (Fin.cases coordinate_160_1 (Fin.cases coordinate_160_2 (Fin.cases coordinate_160_3 (Fin.cases coordinate_160_4 (Fin.cases coordinate_160_5 (Fin.cases coordinate_160_6 (Fin.cases coordinate_160_7 (Fin.cases coordinate_160_8 (Fin.cases coordinate_160_9 (Fin.cases coordinate_160_10 (Fin.cases coordinate_160_11 (Fin.cases coordinate_160_12 (Fin.cases coordinate_160_13 (Fin.cases coordinate_160_14 (Fin.cases coordinate_160_15 (Fin.cases coordinate_160_16 (Fin.cases coordinate_160_17 (Fin.cases coordinate_160_18 (Fin.cases coordinate_160_19 (Fin.cases coordinate_160_20 (Fin.cases coordinate_160_21 (Fin.cases coordinate_160_22 (Fin.cases coordinate_160_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
