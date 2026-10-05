import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear02
import CGLMP5.SOSPhaseLinear12

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_212_0 : commonDenominator 212 / (gramDenominator 70 * phaseDenominator 2) = 20168612178160591503622412459701413249235583654793385708871187565420158508603899971842773799047732360121871933332826099378252920755015732031509332770631370543125727481413362018065413787357355034132725995629282485429553910040653411995271684107014526066812384991869316921569517586709620287537924426998402821481139668784901900683270613324100609915794594662181107203401 := by
  decide +kernel

private theorem scale_212_1 : commonDenominator 212 / (gramDenominator 79 * phaseDenominator 2) = 1 := by
  decide +kernel

private theorem scale_212_2 : commonDenominator 212 / (gramDenominator 80 * phaseDenominator 2) = 14649617754197345294212900979967141924082563095060536037221768139338659885076831831658709083160213242469337329085236963558381451588657897435113923893055055650108938916051675242472155320 := by
  decide +kernel

private theorem scale_212_3 : commonDenominator 212 / (gramDenominator 84 * phaseDenominator 12) = 7835837121786961380964683913627093204210099824364885721087283045422181609613263950207761871369300866865526898675628914940877461871953853025262961779357918110270217067176352366101723002825844521473331356301994812634206644215071984787831637361303124922188441583014163876672146679070850768023042105267069226449185241251002125320794092973702567739774999825235357661388977689509881003275661280193056876084182196781047069147280476329623776644007611045723900754660281897263674077362012446620945278199739070792213757497538555163472004524168431468451577814582390845284338377175000746542555715386324466220500724575270169280293712812000 := by
  decide +kernel

theorem denominator_divides_212 : ∀ f ∈ fiber 212, commonDenominator 212 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_212_0 : integerCoordinateClaim 212 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_0, phase_linear_12_0, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_1 : integerCoordinateClaim 212 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_1, phase_linear_12_1, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_2 : integerCoordinateClaim 212 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_2, phase_linear_12_2, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_3 : integerCoordinateClaim 212 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_3, phase_linear_12_3, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_4 : integerCoordinateClaim 212 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_4, phase_linear_12_4, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_5 : integerCoordinateClaim 212 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_5, phase_linear_12_5, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_6 : integerCoordinateClaim 212 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_6, phase_linear_12_6, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_7 : integerCoordinateClaim 212 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_7, phase_linear_12_7, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_8 : integerCoordinateClaim 212 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_8, phase_linear_12_8, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_9 : integerCoordinateClaim 212 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_9, phase_linear_12_9, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_10 : integerCoordinateClaim 212 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_10, phase_linear_12_10, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_11 : integerCoordinateClaim 212 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_11, phase_linear_12_11, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_12 : integerCoordinateClaim 212 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_12, phase_linear_12_12, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_13 : integerCoordinateClaim 212 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_13, phase_linear_12_13, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_14 : integerCoordinateClaim 212 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_14, phase_linear_12_14, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_15 : integerCoordinateClaim 212 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_15, phase_linear_12_15, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_16 : integerCoordinateClaim 212 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_16, phase_linear_12_16, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_17 : integerCoordinateClaim 212 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_17, phase_linear_12_17, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_18 : integerCoordinateClaim 212 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_18, phase_linear_12_18, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_19 : integerCoordinateClaim 212 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_19, phase_linear_12_19, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_20 : integerCoordinateClaim 212 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_20, phase_linear_12_20, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_21 : integerCoordinateClaim 212 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_21, phase_linear_12_21, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_22 : integerCoordinateClaim 212 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_22, phase_linear_12_22, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

private theorem coordinate_212_23 : integerCoordinateClaim 212 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_212]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_212_0, scale_212_1, scale_212_2, scale_212_3, phase_linear_2_23, phase_linear_12_23, gram_numerator_literal_70, gram_numerator_literal_79, gram_numerator_literal_80, gram_numerator_literal_84, denominator_literal_212, target_denominator_literal_212, target_numerator_literal_212]
  decide +kernel

theorem integer_residual_212 : integerResidualClaim 212 :=
  (Fin.cases coordinate_212_0 (Fin.cases coordinate_212_1 (Fin.cases coordinate_212_2 (Fin.cases coordinate_212_3 (Fin.cases coordinate_212_4 (Fin.cases coordinate_212_5 (Fin.cases coordinate_212_6 (Fin.cases coordinate_212_7 (Fin.cases coordinate_212_8 (Fin.cases coordinate_212_9 (Fin.cases coordinate_212_10 (Fin.cases coordinate_212_11 (Fin.cases coordinate_212_12 (Fin.cases coordinate_212_13 (Fin.cases coordinate_212_14 (Fin.cases coordinate_212_15 (Fin.cases coordinate_212_16 (Fin.cases coordinate_212_17 (Fin.cases coordinate_212_18 (Fin.cases coordinate_212_19 (Fin.cases coordinate_212_20 (Fin.cases coordinate_212_21 (Fin.cases coordinate_212_22 (Fin.cases coordinate_212_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
