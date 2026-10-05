import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear06
import CGLMP5.SOSPhaseLinear16

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_241_0 : commonDenominator 241 / (gramDenominator 70 * phaseDenominator 6) = 20168612178160591503622412459701413249235583654793385708871187565420158508603899971842773799047732360121871933332826099378252920755015732031509332770631370543125727481413362018065413787357355034132725995629282485429553910040653411995271684107014526066812384991869316921569517586709620287537924426998402821481139668784901900683270613324100609915794594662181107203401 := by
  decide +kernel

private theorem scale_241_1 : commonDenominator 241 / (gramDenominator 79 * phaseDenominator 6) = 1 := by
  decide +kernel

private theorem scale_241_2 : commonDenominator 241 / (gramDenominator 80 * phaseDenominator 6) = 14649617754197345294212900979967141924082563095060536037221768139338659885076831831658709083160213242469337329085236963558381451588657897435113923893055055650108938916051675242472155320 := by
  decide +kernel

private theorem scale_241_3 : commonDenominator 241 / (gramDenominator 84 * phaseDenominator 16) = 7835837121786961380964683913627093204210099824364885721087283045422181609613263950207761871369300866865526898675628914940877461871953853025262961779357918110270217067176352366101723002825844521473331356301994812634206644215071984787831637361303124922188441583014163876672146679070850768023042105267069226449185241251002125320794092973702567739774999825235357661388977689509881003275661280193056876084182196781047069147280476329623776644007611045723900754660281897263674077362012446620945278199739070792213757497538555163472004524168431468451577814582390845284338377175000746542555715386324466220500724575270169280293712812000 := by
  decide +kernel

theorem denominator_divides_241 : ∀ f ∈ fiber 241, commonDenominator 241 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_241_0 : integerCoordinateClaim 241 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_0, phase_linear_16_0, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_1 : integerCoordinateClaim 241 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_1, phase_linear_16_1, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_2 : integerCoordinateClaim 241 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_2, phase_linear_16_2, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_3 : integerCoordinateClaim 241 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_3, phase_linear_16_3, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_4 : integerCoordinateClaim 241 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_4, phase_linear_16_4, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_5 : integerCoordinateClaim 241 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_5, phase_linear_16_5, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_6 : integerCoordinateClaim 241 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_6, phase_linear_16_6, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_7 : integerCoordinateClaim 241 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_7, phase_linear_16_7, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_8 : integerCoordinateClaim 241 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_8, phase_linear_16_8, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_9 : integerCoordinateClaim 241 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_9, phase_linear_16_9, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_10 : integerCoordinateClaim 241 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_10, phase_linear_16_10, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_11 : integerCoordinateClaim 241 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_11, phase_linear_16_11, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_12 : integerCoordinateClaim 241 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_12, phase_linear_16_12, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_13 : integerCoordinateClaim 241 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_13, phase_linear_16_13, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_14 : integerCoordinateClaim 241 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_14, phase_linear_16_14, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_15 : integerCoordinateClaim 241 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_15, phase_linear_16_15, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_16 : integerCoordinateClaim 241 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_16, phase_linear_16_16, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_17 : integerCoordinateClaim 241 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_17, phase_linear_16_17, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_18 : integerCoordinateClaim 241 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_18, phase_linear_16_18, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_19 : integerCoordinateClaim 241 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_19, phase_linear_16_19, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_20 : integerCoordinateClaim 241 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_20, phase_linear_16_20, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_21 : integerCoordinateClaim 241 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_21, phase_linear_16_21, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_22 : integerCoordinateClaim 241 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_22, phase_linear_16_22, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

private theorem coordinate_241_23 : integerCoordinateClaim 241 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_241]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_241_0, scale_241_1, scale_241_2, scale_241_3, phase_linear_6_23, phase_linear_16_23, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_241, target_denominator_literal_241, target_numerator_literal_241]
  decide +kernel

theorem integer_residual_241 : integerResidualClaim 241 :=
  (Fin.cases coordinate_241_0 (Fin.cases coordinate_241_1 (Fin.cases coordinate_241_2 (Fin.cases coordinate_241_3 (Fin.cases coordinate_241_4 (Fin.cases coordinate_241_5 (Fin.cases coordinate_241_6 (Fin.cases coordinate_241_7 (Fin.cases coordinate_241_8 (Fin.cases coordinate_241_9 (Fin.cases coordinate_241_10 (Fin.cases coordinate_241_11 (Fin.cases coordinate_241_12 (Fin.cases coordinate_241_13 (Fin.cases coordinate_241_14 (Fin.cases coordinate_241_15 (Fin.cases coordinate_241_16 (Fin.cases coordinate_241_17 (Fin.cases coordinate_241_18 (Fin.cases coordinate_241_19 (Fin.cases coordinate_241_20 (Fin.cases coordinate_241_21 (Fin.cases coordinate_241_22 (Fin.cases coordinate_241_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
