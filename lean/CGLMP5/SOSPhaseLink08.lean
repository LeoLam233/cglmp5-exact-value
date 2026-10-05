import CGLMP5.SOSCompressedCheck08
import CGLMP5.SOSPhaseLinkBase

namespace CGLMP5.SOSFinite
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
lemma source_phase_polynomial_8
(hmul : ∀ a b : Scalar, Scalar.eval (Scalar.mul a b) = Scalar.eval a * Scalar.eval b) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore 8 c)))
      (fun p => Scalar.eval (phase p)) (localTerms 8) =
      (CanonicalData.polynomial 8).map (fun t => (t.1, Scalar.eval t.2)) := by
  have h0 := congrArg Scalar.eval (funext source_phase_8_0)
  have h1 := congrArg Scalar.eval (funext source_phase_8_1)
  have h2 := congrArg Scalar.eval (funext source_phase_8_2)
  have h3 := congrArg Scalar.eval (funext source_phase_8_3)
  have h4 := congrArg Scalar.eval (funext source_phase_8_4)
  have h5 := congrArg Scalar.eval (funext source_phase_8_5)
  have h6 := congrArg Scalar.eval (funext source_phase_8_6)
  have h7 := congrArg Scalar.eval (funext source_phase_8_7)
  simp only [hmul] at h0 h1 h2 h3 h4 h5 h6 h7
  change ([(⟨[], [(0, 2)]⟩, Scalar.eval (core 17) * Scalar.eval (phase 0)),
    (⟨[], [(1, 2)]⟩, Scalar.eval (core 17) * Scalar.eval (phase 6)),
    (⟨[(0, 2)], []⟩, Scalar.eval (core 17) * Scalar.eval (phase 7)),
    (⟨[(0, 3)], [(1, 4)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 0)),
    (⟨[(0, 4)], [(0, 3)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 9)),
    (⟨[(1, 2)], []⟩, Scalar.eval (core 17) * Scalar.eval (phase 13)),
    (⟨[(1, 3)], [(0, 4)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 2)),
    (⟨[(1, 4)], [(1, 3)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 15))] : SOS.Polynomial) =
    [(⟨[], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 8 0)),
    (⟨[], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 8 1)),
    (⟨[(0, 2)], []⟩, Scalar.eval (canonicalCoefficient 8 2)),
    (⟨[(0, 3)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 8 3)),
    (⟨[(0, 4)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 8 4)),
    (⟨[(1, 2)], []⟩, Scalar.eval (canonicalCoefficient 8 5)),
    (⟨[(1, 3)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 8 6)),
    (⟨[(1, 4)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 8 7))]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, phase_zero_eval, mul_one]

end
end CGLMP5.SOSFinite
