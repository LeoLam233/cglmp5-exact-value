import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear04
import CGLMP5.SOSPhaseLinear05

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_153_0 : commonDenominator 153 / (gramDenominator 69 * phaseDenominator 5) = 4 := by
  decide +kernel

private theorem scale_153_1 : commonDenominator 153 / (gramDenominator 77 * phaseDenominator 5) = 4 := by
  decide +kernel

private theorem scale_153_2 : commonDenominator 153 / (gramDenominator 92 * phaseDenominator 4) = 610400739758222720592204207498630913503440128960855668217573672472444161878201326319112878465008885102889055378551540148265893816194079059796413495543960652087872454835486468436339805 := by
  decide +kernel

theorem denominator_divides_153 : ∀ f ∈ fiber 153, commonDenominator 153 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_153_0 : integerCoordinateClaim 153 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_0, phase_linear_5_0, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_1 : integerCoordinateClaim 153 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_1, phase_linear_5_1, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_2 : integerCoordinateClaim 153 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_2, phase_linear_5_2, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_3 : integerCoordinateClaim 153 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_3, phase_linear_5_3, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_4 : integerCoordinateClaim 153 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_4, phase_linear_5_4, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_5 : integerCoordinateClaim 153 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_5, phase_linear_5_5, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_6 : integerCoordinateClaim 153 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_6, phase_linear_5_6, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_7 : integerCoordinateClaim 153 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_7, phase_linear_5_7, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_8 : integerCoordinateClaim 153 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_8, phase_linear_5_8, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_9 : integerCoordinateClaim 153 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_9, phase_linear_5_9, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_10 : integerCoordinateClaim 153 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_10, phase_linear_5_10, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_11 : integerCoordinateClaim 153 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_11, phase_linear_5_11, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_12 : integerCoordinateClaim 153 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_12, phase_linear_5_12, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_13 : integerCoordinateClaim 153 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_13, phase_linear_5_13, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_14 : integerCoordinateClaim 153 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_14, phase_linear_5_14, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_15 : integerCoordinateClaim 153 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_15, phase_linear_5_15, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_16 : integerCoordinateClaim 153 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_16, phase_linear_5_16, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_17 : integerCoordinateClaim 153 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_17, phase_linear_5_17, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_18 : integerCoordinateClaim 153 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_18, phase_linear_5_18, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_19 : integerCoordinateClaim 153 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_19, phase_linear_5_19, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_20 : integerCoordinateClaim 153 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_20, phase_linear_5_20, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_21 : integerCoordinateClaim 153 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_21, phase_linear_5_21, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_22 : integerCoordinateClaim 153 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_22, phase_linear_5_22, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

private theorem coordinate_153_23 : integerCoordinateClaim 153 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_153]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_153_0, scale_153_1, scale_153_2, phase_linear_4_23, phase_linear_5_23, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_153, target_denominator_literal_153, target_numerator_literal_153]
  decide +kernel

theorem integer_residual_153 : integerResidualClaim 153 :=
  (Fin.cases coordinate_153_0 (Fin.cases coordinate_153_1 (Fin.cases coordinate_153_2 (Fin.cases coordinate_153_3 (Fin.cases coordinate_153_4 (Fin.cases coordinate_153_5 (Fin.cases coordinate_153_6 (Fin.cases coordinate_153_7 (Fin.cases coordinate_153_8 (Fin.cases coordinate_153_9 (Fin.cases coordinate_153_10 (Fin.cases coordinate_153_11 (Fin.cases coordinate_153_12 (Fin.cases coordinate_153_13 (Fin.cases coordinate_153_14 (Fin.cases coordinate_153_15 (Fin.cases coordinate_153_16 (Fin.cases coordinate_153_17 (Fin.cases coordinate_153_18 (Fin.cases coordinate_153_19 (Fin.cases coordinate_153_20 (Fin.cases coordinate_153_21 (Fin.cases coordinate_153_22 (Fin.cases coordinate_153_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
