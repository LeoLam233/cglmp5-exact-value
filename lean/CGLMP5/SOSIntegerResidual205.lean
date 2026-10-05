import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear07
import CGLMP5.SOSPhaseLinear08

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_205_0 : commonDenominator 205 / (gramDenominator 66 * phaseDenominator 7) = 1 := by
  decide +kernel

private theorem scale_205_1 : commonDenominator 205 / (gramDenominator 73 * phaseDenominator 7) = 1 := by
  decide +kernel

private theorem scale_205_2 : commonDenominator 205 / (gramDenominator 86 * phaseDenominator 8) = 610400739758222720592204207498630913503440128960855668217573672472444161878201326319112878465008885102889055378551540148265893816194079059796413495543960652087872454835486468436339805 := by
  decide +kernel

theorem denominator_divides_205 : ∀ f ∈ fiber 205, commonDenominator 205 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_205_0 : integerCoordinateClaim 205 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_0, phase_linear_8_0, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_1 : integerCoordinateClaim 205 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_1, phase_linear_8_1, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_2 : integerCoordinateClaim 205 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_2, phase_linear_8_2, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_3 : integerCoordinateClaim 205 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_3, phase_linear_8_3, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_4 : integerCoordinateClaim 205 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_4, phase_linear_8_4, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_5 : integerCoordinateClaim 205 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_5, phase_linear_8_5, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_6 : integerCoordinateClaim 205 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_6, phase_linear_8_6, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_7 : integerCoordinateClaim 205 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_7, phase_linear_8_7, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_8 : integerCoordinateClaim 205 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_8, phase_linear_8_8, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_9 : integerCoordinateClaim 205 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_9, phase_linear_8_9, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_10 : integerCoordinateClaim 205 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_10, phase_linear_8_10, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_11 : integerCoordinateClaim 205 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_11, phase_linear_8_11, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_12 : integerCoordinateClaim 205 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_12, phase_linear_8_12, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_13 : integerCoordinateClaim 205 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_13, phase_linear_8_13, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_14 : integerCoordinateClaim 205 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_14, phase_linear_8_14, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_15 : integerCoordinateClaim 205 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_15, phase_linear_8_15, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_16 : integerCoordinateClaim 205 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_16, phase_linear_8_16, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_17 : integerCoordinateClaim 205 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_17, phase_linear_8_17, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_18 : integerCoordinateClaim 205 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_18, phase_linear_8_18, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_19 : integerCoordinateClaim 205 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_19, phase_linear_8_19, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_20 : integerCoordinateClaim 205 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_20, phase_linear_8_20, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_21 : integerCoordinateClaim 205 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_21, phase_linear_8_21, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_22 : integerCoordinateClaim 205 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_22, phase_linear_8_22, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

private theorem coordinate_205_23 : integerCoordinateClaim 205 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_205]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_205_0, scale_205_1, scale_205_2, phase_linear_7_23, phase_linear_8_23, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_205, target_denominator_literal_205, target_numerator_literal_205]
  decide +kernel

theorem integer_residual_205 : integerResidualClaim 205 :=
  (Fin.cases coordinate_205_0 (Fin.cases coordinate_205_1 (Fin.cases coordinate_205_2 (Fin.cases coordinate_205_3 (Fin.cases coordinate_205_4 (Fin.cases coordinate_205_5 (Fin.cases coordinate_205_6 (Fin.cases coordinate_205_7 (Fin.cases coordinate_205_8 (Fin.cases coordinate_205_9 (Fin.cases coordinate_205_10 (Fin.cases coordinate_205_11 (Fin.cases coordinate_205_12 (Fin.cases coordinate_205_13 (Fin.cases coordinate_205_14 (Fin.cases coordinate_205_15 (Fin.cases coordinate_205_16 (Fin.cases coordinate_205_17 (Fin.cases coordinate_205_18 (Fin.cases coordinate_205_19 (Fin.cases coordinate_205_20 (Fin.cases coordinate_205_21 (Fin.cases coordinate_205_22 (Fin.cases coordinate_205_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
