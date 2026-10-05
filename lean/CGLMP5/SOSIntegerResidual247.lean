import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear15
import CGLMP5.SOSPhaseLinear16

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_247_0 : commonDenominator 247 / (gramDenominator 66 * phaseDenominator 15) = 4 := by
  decide +kernel

private theorem scale_247_1 : commonDenominator 247 / (gramDenominator 73 * phaseDenominator 15) = 4 := by
  decide +kernel

private theorem scale_247_2 : commonDenominator 247 / (gramDenominator 86 * phaseDenominator 16) = 610400739758222720592204207498630913503440128960855668217573672472444161878201326319112878465008885102889055378551540148265893816194079059796413495543960652087872454835486468436339805 := by
  decide +kernel

theorem denominator_divides_247 : ∀ f ∈ fiber 247, commonDenominator 247 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_247_0 : integerCoordinateClaim 247 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_0, phase_linear_16_0, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_1 : integerCoordinateClaim 247 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_1, phase_linear_16_1, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_2 : integerCoordinateClaim 247 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_2, phase_linear_16_2, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_3 : integerCoordinateClaim 247 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_3, phase_linear_16_3, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_4 : integerCoordinateClaim 247 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_4, phase_linear_16_4, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_5 : integerCoordinateClaim 247 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_5, phase_linear_16_5, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_6 : integerCoordinateClaim 247 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_6, phase_linear_16_6, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_7 : integerCoordinateClaim 247 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_7, phase_linear_16_7, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_8 : integerCoordinateClaim 247 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_8, phase_linear_16_8, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_9 : integerCoordinateClaim 247 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_9, phase_linear_16_9, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_10 : integerCoordinateClaim 247 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_10, phase_linear_16_10, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_11 : integerCoordinateClaim 247 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_11, phase_linear_16_11, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_12 : integerCoordinateClaim 247 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_12, phase_linear_16_12, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_13 : integerCoordinateClaim 247 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_13, phase_linear_16_13, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_14 : integerCoordinateClaim 247 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_14, phase_linear_16_14, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_15 : integerCoordinateClaim 247 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_15, phase_linear_16_15, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_16 : integerCoordinateClaim 247 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_16, phase_linear_16_16, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_17 : integerCoordinateClaim 247 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_17, phase_linear_16_17, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_18 : integerCoordinateClaim 247 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_18, phase_linear_16_18, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_19 : integerCoordinateClaim 247 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_19, phase_linear_16_19, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_20 : integerCoordinateClaim 247 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_20, phase_linear_16_20, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_21 : integerCoordinateClaim 247 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_21, phase_linear_16_21, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_22 : integerCoordinateClaim 247 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_22, phase_linear_16_22, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

private theorem coordinate_247_23 : integerCoordinateClaim 247 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_247]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_247_0, scale_247_1, scale_247_2, phase_linear_15_23, phase_linear_16_23, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_247, target_denominator_literal_247, target_numerator_literal_247]
  decide +kernel

theorem integer_residual_247 : integerResidualClaim 247 :=
  (Fin.cases coordinate_247_0 (Fin.cases coordinate_247_1 (Fin.cases coordinate_247_2 (Fin.cases coordinate_247_3 (Fin.cases coordinate_247_4 (Fin.cases coordinate_247_5 (Fin.cases coordinate_247_6 (Fin.cases coordinate_247_7 (Fin.cases coordinate_247_8 (Fin.cases coordinate_247_9 (Fin.cases coordinate_247_10 (Fin.cases coordinate_247_11 (Fin.cases coordinate_247_12 (Fin.cases coordinate_247_13 (Fin.cases coordinate_247_14 (Fin.cases coordinate_247_15 (Fin.cases coordinate_247_16 (Fin.cases coordinate_247_17 (Fin.cases coordinate_247_18 (Fin.cases coordinate_247_19 (Fin.cases coordinate_247_20 (Fin.cases coordinate_247_21 (Fin.cases coordinate_247_22 (Fin.cases coordinate_247_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
