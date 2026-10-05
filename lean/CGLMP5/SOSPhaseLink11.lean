import CGLMP5.SOSCompressedCheck11
import CGLMP5.SOSPhaseLinkBase

namespace CGLMP5.SOSFinite
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
lemma source_phase_polynomial_11
(hmul : ∀ a b : Scalar, Scalar.eval (Scalar.mul a b) = Scalar.eval a * Scalar.eval b) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore 11 c)))
      (fun p => Scalar.eval (phase p)) (localTerms 11) =
      (CanonicalData.polynomial 11).map (fun t => (t.1, Scalar.eval t.2)) := by
  have h0 := congrArg Scalar.eval (funext source_phase_11_0)
  have h1 := congrArg Scalar.eval (funext source_phase_11_1)
  have h2 := congrArg Scalar.eval (funext source_phase_11_2)
  have h3 := congrArg Scalar.eval (funext source_phase_11_3)
  simp only [hmul] at h0 h1 h2 h3
  change ([(⟨[(0, 4)], [(0, 4)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 0)),
    (⟨[(0, 4)], [(1, 4)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 12)),
    (⟨[(1, 4)], [(0, 4)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 12)),
    (⟨[(1, 4)], [(1, 4)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 4))] : SOS.Polynomial) =
    [(⟨[(0, 4)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 11 0)),
    (⟨[(0, 4)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 11 1)),
    (⟨[(1, 4)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 11 2)),
    (⟨[(1, 4)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 11 3))]
  simp only [h0, h1, h2, h3, phase_zero_eval, mul_one]

end
end CGLMP5.SOSFinite
