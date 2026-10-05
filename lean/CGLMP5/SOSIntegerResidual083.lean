import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear08
import CGLMP5.SOSPhaseLinear18

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_83_0 : commonDenominator 83 / (gramDenominator 70 * phaseDenominator 18) = 20168612178160591503622412459701413249235583654793385708871187565420158508603899971842773799047732360121871933332826099378252920755015732031509332770631370543125727481413362018065413787357355034132725995629282485429553910040653411995271684107014526066812384991869316921569517586709620287537924426998402821481139668784901900683270613324100609915794594662181107203401 := by
  decide +kernel

private theorem scale_83_1 : commonDenominator 83 / (gramDenominator 79 * phaseDenominator 18) = 1 := by
  decide +kernel

private theorem scale_83_2 : commonDenominator 83 / (gramDenominator 80 * phaseDenominator 18) = 14649617754197345294212900979967141924082563095060536037221768139338659885076831831658709083160213242469337329085236963558381451588657897435113923893055055650108938916051675242472155320 := by
  decide +kernel

private theorem scale_83_3 : commonDenominator 83 / (gramDenominator 84 * phaseDenominator 8) = 7835837121786961380964683913627093204210099824364885721087283045422181609613263950207761871369300866865526898675628914940877461871953853025262961779357918110270217067176352366101723002825844521473331356301994812634206644215071984787831637361303124922188441583014163876672146679070850768023042105267069226449185241251002125320794092973702567739774999825235357661388977689509881003275661280193056876084182196781047069147280476329623776644007611045723900754660281897263674077362012446620945278199739070792213757497538555163472004524168431468451577814582390845284338377175000746542555715386324466220500724575270169280293712812000 := by
  decide +kernel

theorem denominator_divides_083 : ∀ f ∈ fiber 83, commonDenominator 83 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_83_0 : integerCoordinateClaim 83 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_0, phase_linear_18_0, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_1 : integerCoordinateClaim 83 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_1, phase_linear_18_1, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_2 : integerCoordinateClaim 83 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_2, phase_linear_18_2, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_3 : integerCoordinateClaim 83 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_3, phase_linear_18_3, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_4 : integerCoordinateClaim 83 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_4, phase_linear_18_4, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_5 : integerCoordinateClaim 83 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_5, phase_linear_18_5, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_6 : integerCoordinateClaim 83 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_6, phase_linear_18_6, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_7 : integerCoordinateClaim 83 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_7, phase_linear_18_7, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_8 : integerCoordinateClaim 83 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_8, phase_linear_18_8, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_9 : integerCoordinateClaim 83 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_9, phase_linear_18_9, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_10 : integerCoordinateClaim 83 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_10, phase_linear_18_10, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_11 : integerCoordinateClaim 83 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_11, phase_linear_18_11, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_12 : integerCoordinateClaim 83 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_12, phase_linear_18_12, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_13 : integerCoordinateClaim 83 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_13, phase_linear_18_13, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_14 : integerCoordinateClaim 83 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_14, phase_linear_18_14, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_15 : integerCoordinateClaim 83 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_15, phase_linear_18_15, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_16 : integerCoordinateClaim 83 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_16, phase_linear_18_16, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_17 : integerCoordinateClaim 83 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_17, phase_linear_18_17, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_18 : integerCoordinateClaim 83 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_18, phase_linear_18_18, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_19 : integerCoordinateClaim 83 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_19, phase_linear_18_19, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_20 : integerCoordinateClaim 83 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_20, phase_linear_18_20, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_21 : integerCoordinateClaim 83 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_21, phase_linear_18_21, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_22 : integerCoordinateClaim 83 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_22, phase_linear_18_22, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

private theorem coordinate_83_23 : integerCoordinateClaim 83 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_83]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_83_0, scale_83_1, scale_83_2, scale_83_3, phase_linear_8_23, phase_linear_18_23, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_83, target_denominator_literal_83, target_numerator_literal_83]
  decide +kernel

theorem integer_residual_083 : integerResidualClaim 83 :=
  (Fin.cases coordinate_83_0 (Fin.cases coordinate_83_1 (Fin.cases coordinate_83_2 (Fin.cases coordinate_83_3 (Fin.cases coordinate_83_4 (Fin.cases coordinate_83_5 (Fin.cases coordinate_83_6 (Fin.cases coordinate_83_7 (Fin.cases coordinate_83_8 (Fin.cases coordinate_83_9 (Fin.cases coordinate_83_10 (Fin.cases coordinate_83_11 (Fin.cases coordinate_83_12 (Fin.cases coordinate_83_13 (Fin.cases coordinate_83_14 (Fin.cases coordinate_83_15 (Fin.cases coordinate_83_16 (Fin.cases coordinate_83_17 (Fin.cases coordinate_83_18 (Fin.cases coordinate_83_19 (Fin.cases coordinate_83_20 (Fin.cases coordinate_83_21 (Fin.cases coordinate_83_22 (Fin.cases coordinate_83_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
