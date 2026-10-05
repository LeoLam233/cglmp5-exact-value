import CGLMP5.CanonicalData
import CGLMP5.EmbeddingBounds

/-!
# Strict positivity of all fourteen source-bound compact weights

All enclosures are rational expressions evaluated by Lean's kernel. They are
interpreted in the actual positive embedding by `ProofBounds.scalar_enclosure`.
-/

namespace CGLMP5

/-- The real value of the exact serialized compact weight. -/
noncomputable def weightValue (j : Fin 14) : ℝ := Scalar.evalReal (CanonicalData.weight j)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
lemma weight_enclosure_lower (j : Fin 14) :
    (1/3000 : ℚ) < (Scalar.enclosure ProofBounds.sI ProofBounds.xI ProofBounds.uI
      (CanonicalData.weight j)).lo := by
  fin_cases j <;> decide +kernel

lemma weight_gt_one_div_three_thousand (j : Fin 14) : (1/3000 : ℝ) < weightValue j := by
  have h := (ProofBounds.scalar_enclosure (CanonicalData.weight j)).1
  have hp : (1/3000 : ℝ) <
      ((Scalar.enclosure ProofBounds.sI ProofBounds.xI ProofBounds.uI
        (CanonicalData.weight j)).lo : ℝ) := by
    have hr := (Rat.cast_lt (K := ℝ)).mpr (weight_enclosure_lower j)
    norm_num at hr ⊢
    exact hr
  exact lt_of_lt_of_le hp h

lemma weight_positive (j : Fin 14) : 0 < weightValue j :=
  lt_trans (by norm_num) (weight_gt_one_div_three_thousand j)

lemma weight_evaluation (j : Fin 14) :
    Scalar.eval (CanonicalData.weight j) = (weightValue j : ℂ) :=
  Scalar.eval_eq_ofReal _ (CanonicalData.weight_isReal j)

end CGLMP5
