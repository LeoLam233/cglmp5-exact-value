import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear08
import CGLMP5.SOSPhaseLinear18

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_137_0 : commonDenominator 137 / (gramDenominator 63 * phaseDenominator 18) = 15669104184502887809234468142794378350810551207496649093893187509776968176974438441 := by
  decide +kernel

private theorem scale_137_1 : commonDenominator 137 / (gramDenominator 98 * phaseDenominator 8) = 1 := by
  decide +kernel

private theorem scale_137_2 : commonDenominator 137 / (gramDenominator 106 * phaseDenominator 8) = 1 := by
  decide +kernel

theorem denominator_divides_137 : ∀ f ∈ fiber 137, commonDenominator 137 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_137_0 : integerCoordinateClaim 137 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_0, phase_linear_18_0, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_1 : integerCoordinateClaim 137 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_1, phase_linear_18_1, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_2 : integerCoordinateClaim 137 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_2, phase_linear_18_2, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_3 : integerCoordinateClaim 137 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_3, phase_linear_18_3, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_4 : integerCoordinateClaim 137 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_4, phase_linear_18_4, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_5 : integerCoordinateClaim 137 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_5, phase_linear_18_5, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_6 : integerCoordinateClaim 137 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_6, phase_linear_18_6, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_7 : integerCoordinateClaim 137 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_7, phase_linear_18_7, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_8 : integerCoordinateClaim 137 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_8, phase_linear_18_8, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_9 : integerCoordinateClaim 137 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_9, phase_linear_18_9, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_10 : integerCoordinateClaim 137 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_10, phase_linear_18_10, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_11 : integerCoordinateClaim 137 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_11, phase_linear_18_11, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_12 : integerCoordinateClaim 137 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_12, phase_linear_18_12, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_13 : integerCoordinateClaim 137 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_13, phase_linear_18_13, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_14 : integerCoordinateClaim 137 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_14, phase_linear_18_14, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_15 : integerCoordinateClaim 137 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_15, phase_linear_18_15, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_16 : integerCoordinateClaim 137 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_16, phase_linear_18_16, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_17 : integerCoordinateClaim 137 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_17, phase_linear_18_17, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_18 : integerCoordinateClaim 137 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_18, phase_linear_18_18, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_19 : integerCoordinateClaim 137 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_19, phase_linear_18_19, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_20 : integerCoordinateClaim 137 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_20, phase_linear_18_20, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_21 : integerCoordinateClaim 137 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_21, phase_linear_18_21, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_22 : integerCoordinateClaim 137 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_22, phase_linear_18_22, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

private theorem coordinate_137_23 : integerCoordinateClaim 137 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_137]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_137_0, scale_137_1, scale_137_2, phase_linear_8_23, phase_linear_18_23, gram_numerator_literal_63, gram_numerator_literal_98, gram_numerator_literal_106, denominator_literal_137, target_denominator_literal_137, target_numerator_literal_137]
  decide +kernel

theorem integer_residual_137 : integerResidualClaim 137 :=
  (Fin.cases coordinate_137_0 (Fin.cases coordinate_137_1 (Fin.cases coordinate_137_2 (Fin.cases coordinate_137_3 (Fin.cases coordinate_137_4 (Fin.cases coordinate_137_5 (Fin.cases coordinate_137_6 (Fin.cases coordinate_137_7 (Fin.cases coordinate_137_8 (Fin.cases coordinate_137_9 (Fin.cases coordinate_137_10 (Fin.cases coordinate_137_11 (Fin.cases coordinate_137_12 (Fin.cases coordinate_137_13 (Fin.cases coordinate_137_14 (Fin.cases coordinate_137_15 (Fin.cases coordinate_137_16 (Fin.cases coordinate_137_17 (Fin.cases coordinate_137_18 (Fin.cases coordinate_137_19 (Fin.cases coordinate_137_20 (Fin.cases coordinate_137_21 (Fin.cases coordinate_137_22 (Fin.cases coordinate_137_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
