import CGLMP5.ScalarDefs
import CGLMP5.SOSGramSemantics
import CGLMP5.SOSCompressedData
namespace CGLMP5.SOSFinite
noncomputable section
lemma phase_zero_eval : Scalar.eval (phase 0) = 1 := by
  have h : phase 0 = Scalar.ofRat 1 := by
    funext k
    fin_cases k <;> norm_num [phase, Scalar.ofRat, Scalar.ofCanonical]
  rw [h, Scalar.eval_ofRat]
  norm_num
end
end CGLMP5.SOSFinite
