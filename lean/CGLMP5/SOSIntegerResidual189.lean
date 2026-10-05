import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear12
import CGLMP5.SOSPhaseLinear13

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_189_0 : commonDenominator 189 / (gramDenominator 69 * phaseDenominator 13) = 1 := by
  decide +kernel

private theorem scale_189_1 : commonDenominator 189 / (gramDenominator 77 * phaseDenominator 13) = 1 := by
  decide +kernel

private theorem scale_189_2 : commonDenominator 189 / (gramDenominator 92 * phaseDenominator 12) = 610400739758222720592204207498630913503440128960855668217573672472444161878201326319112878465008885102889055378551540148265893816194079059796413495543960652087872454835486468436339805 := by
  decide +kernel

theorem denominator_divides_189 : ∀ f ∈ fiber 189, commonDenominator 189 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_189_0 : integerCoordinateClaim 189 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_0, phase_linear_13_0, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_1 : integerCoordinateClaim 189 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_1, phase_linear_13_1, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_2 : integerCoordinateClaim 189 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_2, phase_linear_13_2, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_3 : integerCoordinateClaim 189 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_3, phase_linear_13_3, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_4 : integerCoordinateClaim 189 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_4, phase_linear_13_4, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_5 : integerCoordinateClaim 189 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_5, phase_linear_13_5, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_6 : integerCoordinateClaim 189 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_6, phase_linear_13_6, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_7 : integerCoordinateClaim 189 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_7, phase_linear_13_7, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_8 : integerCoordinateClaim 189 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_8, phase_linear_13_8, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_9 : integerCoordinateClaim 189 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_9, phase_linear_13_9, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_10 : integerCoordinateClaim 189 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_10, phase_linear_13_10, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_11 : integerCoordinateClaim 189 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_11, phase_linear_13_11, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_12 : integerCoordinateClaim 189 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_12, phase_linear_13_12, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_13 : integerCoordinateClaim 189 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_13, phase_linear_13_13, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_14 : integerCoordinateClaim 189 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_14, phase_linear_13_14, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_15 : integerCoordinateClaim 189 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_15, phase_linear_13_15, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_16 : integerCoordinateClaim 189 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_16, phase_linear_13_16, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_17 : integerCoordinateClaim 189 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_17, phase_linear_13_17, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_18 : integerCoordinateClaim 189 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_18, phase_linear_13_18, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_19 : integerCoordinateClaim 189 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_19, phase_linear_13_19, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_20 : integerCoordinateClaim 189 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_20, phase_linear_13_20, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_21 : integerCoordinateClaim 189 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_21, phase_linear_13_21, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_22 : integerCoordinateClaim 189 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_22, phase_linear_13_22, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

private theorem coordinate_189_23 : integerCoordinateClaim 189 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_189]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_189_0, scale_189_1, scale_189_2, phase_linear_12_23, phase_linear_13_23, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_189, target_denominator_literal_189, target_numerator_literal_189]
  decide +kernel

theorem integer_residual_189 : integerResidualClaim 189 :=
  (Fin.cases coordinate_189_0 (Fin.cases coordinate_189_1 (Fin.cases coordinate_189_2 (Fin.cases coordinate_189_3 (Fin.cases coordinate_189_4 (Fin.cases coordinate_189_5 (Fin.cases coordinate_189_6 (Fin.cases coordinate_189_7 (Fin.cases coordinate_189_8 (Fin.cases coordinate_189_9 (Fin.cases coordinate_189_10 (Fin.cases coordinate_189_11 (Fin.cases coordinate_189_12 (Fin.cases coordinate_189_13 (Fin.cases coordinate_189_14 (Fin.cases coordinate_189_15 (Fin.cases coordinate_189_16 (Fin.cases coordinate_189_17 (Fin.cases coordinate_189_18 (Fin.cases coordinate_189_19 (Fin.cases coordinate_189_20 (Fin.cases coordinate_189_21 (Fin.cases coordinate_189_22 (Fin.cases coordinate_189_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
