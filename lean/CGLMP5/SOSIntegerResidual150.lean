import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear07
import CGLMP5.SOSPhaseLinear08

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_150_0 : commonDenominator 150 / (gramDenominator 66 * phaseDenominator 7) = 1 := by
  decide +kernel

private theorem scale_150_1 : commonDenominator 150 / (gramDenominator 73 * phaseDenominator 7) = 1 := by
  decide +kernel

private theorem scale_150_2 : commonDenominator 150 / (gramDenominator 86 * phaseDenominator 8) = 610400739758222720592204207498630913503440128960855668217573672472444161878201326319112878465008885102889055378551540148265893816194079059796413495543960652087872454835486468436339805 := by
  decide +kernel

theorem denominator_divides_150 : ∀ f ∈ fiber 150, commonDenominator 150 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_150_0 : integerCoordinateClaim 150 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_0, phase_linear_8_0, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_1 : integerCoordinateClaim 150 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_1, phase_linear_8_1, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_2 : integerCoordinateClaim 150 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_2, phase_linear_8_2, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_3 : integerCoordinateClaim 150 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_3, phase_linear_8_3, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_4 : integerCoordinateClaim 150 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_4, phase_linear_8_4, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_5 : integerCoordinateClaim 150 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_5, phase_linear_8_5, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_6 : integerCoordinateClaim 150 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_6, phase_linear_8_6, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_7 : integerCoordinateClaim 150 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_7, phase_linear_8_7, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_8 : integerCoordinateClaim 150 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_8, phase_linear_8_8, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_9 : integerCoordinateClaim 150 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_9, phase_linear_8_9, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_10 : integerCoordinateClaim 150 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_10, phase_linear_8_10, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_11 : integerCoordinateClaim 150 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_11, phase_linear_8_11, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_12 : integerCoordinateClaim 150 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_12, phase_linear_8_12, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_13 : integerCoordinateClaim 150 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_13, phase_linear_8_13, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_14 : integerCoordinateClaim 150 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_14, phase_linear_8_14, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_15 : integerCoordinateClaim 150 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_15, phase_linear_8_15, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_16 : integerCoordinateClaim 150 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_16, phase_linear_8_16, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_17 : integerCoordinateClaim 150 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_17, phase_linear_8_17, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_18 : integerCoordinateClaim 150 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_18, phase_linear_8_18, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_19 : integerCoordinateClaim 150 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_19, phase_linear_8_19, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_20 : integerCoordinateClaim 150 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_20, phase_linear_8_20, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_21 : integerCoordinateClaim 150 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_21, phase_linear_8_21, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_22 : integerCoordinateClaim 150 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_22, phase_linear_8_22, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

private theorem coordinate_150_23 : integerCoordinateClaim 150 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_150]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_150_0, scale_150_1, scale_150_2, phase_linear_7_23, phase_linear_8_23, gram_numerator_literal_66, gram_numerator_literal_73, gram_numerator_literal_86, denominator_literal_150, target_denominator_literal_150, target_numerator_literal_150]
  decide +kernel

theorem integer_residual_150 : integerResidualClaim 150 :=
  (Fin.cases coordinate_150_0 (Fin.cases coordinate_150_1 (Fin.cases coordinate_150_2 (Fin.cases coordinate_150_3 (Fin.cases coordinate_150_4 (Fin.cases coordinate_150_5 (Fin.cases coordinate_150_6 (Fin.cases coordinate_150_7 (Fin.cases coordinate_150_8 (Fin.cases coordinate_150_9 (Fin.cases coordinate_150_10 (Fin.cases coordinate_150_11 (Fin.cases coordinate_150_12 (Fin.cases coordinate_150_13 (Fin.cases coordinate_150_14 (Fin.cases coordinate_150_15 (Fin.cases coordinate_150_16 (Fin.cases coordinate_150_17 (Fin.cases coordinate_150_18 (Fin.cases coordinate_150_19 (Fin.cases coordinate_150_20 (Fin.cases coordinate_150_21 (Fin.cases coordinate_150_22 (Fin.cases coordinate_150_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
