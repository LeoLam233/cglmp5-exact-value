import CGLMP5.Scalar
import CGLMP5.SOSPhaseLink00
import CGLMP5.SOSPhaseLink01
import CGLMP5.SOSPhaseLink02
import CGLMP5.SOSPhaseLink03
import CGLMP5.SOSPhaseLink04
import CGLMP5.SOSPhaseLink05
import CGLMP5.SOSPhaseLink06
import CGLMP5.SOSPhaseLink07
import CGLMP5.SOSPhaseLink08
import CGLMP5.SOSPhaseLink09
import CGLMP5.SOSPhaseLink10
import CGLMP5.SOSPhaseLink11
import CGLMP5.SOSPhaseLink12
import CGLMP5.SOSPhaseLink13

namespace CGLMP5.SOSFinite
noncomputable section
lemma phasePolynomial_eq_canonical (j : Fin 14) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore j c)))
      (fun p => Scalar.eval (phase p)) (localTerms j) =
      (CanonicalData.polynomial j).map (fun t => (t.1, Scalar.eval t.2)) := by
  fin_cases j
  · exact source_phase_polynomial_0 Scalar.eval_mul
  · exact source_phase_polynomial_1 Scalar.eval_mul
  · exact source_phase_polynomial_2 Scalar.eval_mul
  · exact source_phase_polynomial_3 Scalar.eval_mul
  · exact source_phase_polynomial_4 Scalar.eval_mul
  · exact source_phase_polynomial_5 Scalar.eval_mul
  · exact source_phase_polynomial_6 Scalar.eval_mul
  · exact source_phase_polynomial_7 Scalar.eval_mul
  · exact source_phase_polynomial_8 Scalar.eval_mul
  · exact source_phase_polynomial_9 Scalar.eval_mul
  · exact source_phase_polynomial_10 Scalar.eval_mul
  · exact source_phase_polynomial_11 Scalar.eval_mul
  · exact source_phase_polynomial_12 Scalar.eval_mul
  · exact source_phase_polynomial_13 Scalar.eval_mul
end
end CGLMP5.SOSFinite
