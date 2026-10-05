import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear15
import CGLMP5.SOSPhaseLinear16

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_57_0 : commonDenominator 57 / (gramDenominator 66 * phaseDenominator 15) = 4 := by
  decide +kernel

private theorem scale_57_1 : commonDenominator 57 / (gramDenominator 73 * phaseDenominator 15) = 4 := by
  decide +kernel

private theorem scale_57_2 : commonDenominator 57 / (gramDenominator 86 * phaseDenominator 16) = 610400739758222720592204207498630913503440128960855668217573672472444161878201326319112878465008885102889055378551540148265893816194079059796413495543960652087872454835486468436339805 := by
  decide +kernel

theorem denominator_divides_057 : ∀ f ∈ fiber 57, commonDenominator 57 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_57_0 : integerCoordinateClaim 57 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_0, phase_linear_16_0, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_1 : integerCoordinateClaim 57 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_1, phase_linear_16_1, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_2 : integerCoordinateClaim 57 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_2, phase_linear_16_2, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_3 : integerCoordinateClaim 57 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_3, phase_linear_16_3, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_4 : integerCoordinateClaim 57 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_4, phase_linear_16_4, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_5 : integerCoordinateClaim 57 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_5, phase_linear_16_5, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_6 : integerCoordinateClaim 57 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_6, phase_linear_16_6, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_7 : integerCoordinateClaim 57 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_7, phase_linear_16_7, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_8 : integerCoordinateClaim 57 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_8, phase_linear_16_8, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_9 : integerCoordinateClaim 57 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_9, phase_linear_16_9, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_10 : integerCoordinateClaim 57 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_10, phase_linear_16_10, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_11 : integerCoordinateClaim 57 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_11, phase_linear_16_11, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_12 : integerCoordinateClaim 57 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_12, phase_linear_16_12, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_13 : integerCoordinateClaim 57 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_13, phase_linear_16_13, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_14 : integerCoordinateClaim 57 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_14, phase_linear_16_14, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_15 : integerCoordinateClaim 57 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_15, phase_linear_16_15, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_16 : integerCoordinateClaim 57 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_16, phase_linear_16_16, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_17 : integerCoordinateClaim 57 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_17, phase_linear_16_17, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_18 : integerCoordinateClaim 57 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_18, phase_linear_16_18, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_19 : integerCoordinateClaim 57 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_19, phase_linear_16_19, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_20 : integerCoordinateClaim 57 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_20, phase_linear_16_20, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_21 : integerCoordinateClaim 57 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_21, phase_linear_16_21, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_22 : integerCoordinateClaim 57 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_22, phase_linear_16_22, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

private theorem coordinate_57_23 : integerCoordinateClaim 57 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_57]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_57_0, scale_57_1, scale_57_2, phase_linear_15_23, phase_linear_16_23, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_57, target_denominator_literal_57, target_numerator_literal_57]
  decide +kernel

theorem integer_residual_057 : integerResidualClaim 57 :=
  (Fin.cases coordinate_57_0 (Fin.cases coordinate_57_1 (Fin.cases coordinate_57_2 (Fin.cases coordinate_57_3 (Fin.cases coordinate_57_4 (Fin.cases coordinate_57_5 (Fin.cases coordinate_57_6 (Fin.cases coordinate_57_7 (Fin.cases coordinate_57_8 (Fin.cases coordinate_57_9 (Fin.cases coordinate_57_10 (Fin.cases coordinate_57_11 (Fin.cases coordinate_57_12 (Fin.cases coordinate_57_13 (Fin.cases coordinate_57_14 (Fin.cases coordinate_57_15 (Fin.cases coordinate_57_16 (Fin.cases coordinate_57_17 (Fin.cases coordinate_57_18 (Fin.cases coordinate_57_19 (Fin.cases coordinate_57_20 (Fin.cases coordinate_57_21 (Fin.cases coordinate_57_22 (Fin.cases coordinate_57_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
