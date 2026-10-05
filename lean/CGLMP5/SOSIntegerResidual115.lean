import CGLMP5.SOSIntegerLiterals
import CGLMP5.SOSPhaseLinear12
import CGLMP5.SOSPhaseLinear13

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem scale_115_0 : commonDenominator 115 / (gramDenominator 69 * phaseDenominator 13) = 1 := by
  decide +kernel

private theorem scale_115_1 : commonDenominator 115 / (gramDenominator 77 * phaseDenominator 13) = 1 := by
  decide +kernel

private theorem scale_115_2 : commonDenominator 115 / (gramDenominator 92 * phaseDenominator 12) = 610400739758222720592204207498630913503440128960855668217573672472444161878201326319112878465008885102889055378551540148265893816194079059796413495543960652087872454835486468436339805 := by
  decide +kernel

theorem denominator_divides_115 : ∀ f ∈ fiber 115, commonDenominator 115 % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by
  decide +kernel

private theorem coordinate_115_0 : integerCoordinateClaim 115 0 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_0, phase_linear_13_0, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_1 : integerCoordinateClaim 115 1 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_1, phase_linear_13_1, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_2 : integerCoordinateClaim 115 2 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_2, phase_linear_13_2, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_3 : integerCoordinateClaim 115 3 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_3, phase_linear_13_3, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_4 : integerCoordinateClaim 115 4 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_4, phase_linear_13_4, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_5 : integerCoordinateClaim 115 5 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_5, phase_linear_13_5, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_6 : integerCoordinateClaim 115 6 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_6, phase_linear_13_6, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_7 : integerCoordinateClaim 115 7 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_7, phase_linear_13_7, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_8 : integerCoordinateClaim 115 8 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_8, phase_linear_13_8, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_9 : integerCoordinateClaim 115 9 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_9, phase_linear_13_9, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_10 : integerCoordinateClaim 115 10 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_10, phase_linear_13_10, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_11 : integerCoordinateClaim 115 11 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_11, phase_linear_13_11, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_12 : integerCoordinateClaim 115 12 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_12, phase_linear_13_12, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_13 : integerCoordinateClaim 115 13 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_13, phase_linear_13_13, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_14 : integerCoordinateClaim 115 14 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_14, phase_linear_13_14, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_15 : integerCoordinateClaim 115 15 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_15, phase_linear_13_15, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_16 : integerCoordinateClaim 115 16 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_16, phase_linear_13_16, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_17 : integerCoordinateClaim 115 17 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_17, phase_linear_13_17, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_18 : integerCoordinateClaim 115 18 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_18, phase_linear_13_18, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_19 : integerCoordinateClaim 115 19 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_19, phase_linear_13_19, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_20 : integerCoordinateClaim 115 20 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_20, phase_linear_13_20, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_21 : integerCoordinateClaim 115 21 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_21, phase_linear_13_21, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_22 : integerCoordinateClaim 115 22 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_22, phase_linear_13_22, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

private theorem coordinate_115_23 : integerCoordinateClaim 115 23 := by
  unfold integerCoordinateClaim
  rw [integerNumerator, fiber_literal_115]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, scale_115_0, scale_115_1, scale_115_2, phase_linear_12_23, phase_linear_13_23, gram_numerator_literal_69, gram_numerator_literal_77, gram_numerator_literal_92, denominator_literal_115, target_denominator_literal_115, target_numerator_literal_115]
  decide +kernel

theorem integer_residual_115 : integerResidualClaim 115 :=
  (Fin.cases coordinate_115_0 (Fin.cases coordinate_115_1 (Fin.cases coordinate_115_2 (Fin.cases coordinate_115_3 (Fin.cases coordinate_115_4 (Fin.cases coordinate_115_5 (Fin.cases coordinate_115_6 (Fin.cases coordinate_115_7 (Fin.cases coordinate_115_8 (Fin.cases coordinate_115_9 (Fin.cases coordinate_115_10 (Fin.cases coordinate_115_11 (Fin.cases coordinate_115_12 (Fin.cases coordinate_115_13 (Fin.cases coordinate_115_14 (Fin.cases coordinate_115_15 (Fin.cases coordinate_115_16 (Fin.cases coordinate_115_17 (Fin.cases coordinate_115_18 (Fin.cases coordinate_115_19 (Fin.cases coordinate_115_20 (Fin.cases coordinate_115_21 (Fin.cases coordinate_115_22 (Fin.cases coordinate_115_23 (fun i => Fin.elim0 i)))))))))))))))))))))))))

end CGLMP5.SOSFinite
