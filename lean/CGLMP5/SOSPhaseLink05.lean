import CGLMP5.SOSCompressedCheck05
import CGLMP5.SOSPhaseLinkBase

namespace CGLMP5.SOSFinite
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
lemma source_phase_polynomial_5
(hmul : ∀ a b : Scalar, Scalar.eval (Scalar.mul a b) = Scalar.eval a * Scalar.eval b) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore 5 c)))
      (fun p => Scalar.eval (phase p)) (localTerms 5) =
      (CanonicalData.polynomial 5).map (fun t => (t.1, Scalar.eval t.2)) := by
  have h0 := congrArg Scalar.eval (funext source_phase_5_0)
  have h1 := congrArg Scalar.eval (funext source_phase_5_1)
  have h2 := congrArg Scalar.eval (funext source_phase_5_2)
  have h3 := congrArg Scalar.eval (funext source_phase_5_3)
  simp only [hmul] at h0 h1 h2 h3
  change ([(⟨[(0, 3)], [(0, 3)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 0)),
    (⟨[(0, 3)], [(1, 3)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 14)),
    (⟨[(1, 3)], [(0, 3)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 14)),
    (⟨[(1, 3)], [(1, 3)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 8))] : SOS.Polynomial) =
    [(⟨[(0, 3)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 5 0)),
    (⟨[(0, 3)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 5 1)),
    (⟨[(1, 3)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 5 2)),
    (⟨[(1, 3)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 5 3))]
  simp only [h0, h1, h2, h3, phase_zero_eval, mul_one]

end
end CGLMP5.SOSFinite
