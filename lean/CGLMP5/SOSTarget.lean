import CGLMP5.SOSTargetCoefficients

namespace CGLMP5.SOSFinite

set_option maxRecDepth 20000

/-- The concrete reflected target evaluates to the published Bell gap in every
complex star-algebra. This statement introduces no operator relations. -/
lemma target_evaluation {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
    (a b : Fin 2 → unitary R) :
    SOS.evaluate a b (targetPolynomial.map fun t => (t.1, Scalar.eval t.2)) =
      (mu : ℂ) • (1 : R) - SOS.bell (zeta^4) a b := by
  have hfr : List.finRange 4 = [0,1,2,3] := by decide
  have hone : Word.evalStar a b Word.one = (1:R) := by
    simp [Word.evalStar]
  unfold SOS.evaluate
  rw [target_layout]
  simp only [List.map_cons, List.map_flatMap, List.map_map, Function.comp_def,
    List.sum_cons, Prod.fst, Prod.snd, Scalar.eval_mu, hone]
  simp_rw [targetEdge_eval]
  simp only [hfr, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.append_nil, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil,
    SOS.bell, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, zero_add]
  simp only [neg_smul]
  abel

end CGLMP5.SOSFinite
