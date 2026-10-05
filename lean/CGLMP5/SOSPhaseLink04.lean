import CGLMP5.SOSCompressedCheck04
import CGLMP5.SOSPhaseLinkBase

namespace CGLMP5.SOSFinite
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
lemma source_phase_polynomial_4
(hmul : ∀ a b : Scalar, Scalar.eval (Scalar.mul a b) = Scalar.eval a * Scalar.eval b) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore 4 c)))
      (fun p => Scalar.eval (phase p)) (localTerms 4) =
      (CanonicalData.polynomial 4).map (fun t => (t.1, Scalar.eval t.2)) := by
  have h0 := congrArg Scalar.eval (funext source_phase_4_0)
  have h1 := congrArg Scalar.eval (funext source_phase_4_1)
  have h2 := congrArg Scalar.eval (funext source_phase_4_2)
  have h3 := congrArg Scalar.eval (funext source_phase_4_3)
  have h4 := congrArg Scalar.eval (funext source_phase_4_4)
  have h5 := congrArg Scalar.eval (funext source_phase_4_5)
  have h6 := congrArg Scalar.eval (funext source_phase_4_6)
  have h7 := congrArg Scalar.eval (funext source_phase_4_7)
  simp only [hmul] at h0 h1 h2 h3 h4 h5 h6 h7
  change ([(⟨[(0, 2)], [(1, 4)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 0)),
    (⟨[(0, 3)], [(0, 3)]⟩, Scalar.eval (core 11) * Scalar.eval (phase 0)),
    (⟨[(0, 3)], [(1, 3)]⟩, Scalar.eval (core 11) * Scalar.eval (phase 14)),
    (⟨[(0, 4)], [(0, 2)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 10)),
    (⟨[(1, 2)], [(0, 4)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 4)),
    (⟨[(1, 3)], [(0, 3)]⟩, Scalar.eval (core 11) * Scalar.eval (phase 14)),
    (⟨[(1, 3)], [(1, 3)]⟩, Scalar.eval (core 11) * Scalar.eval (phase 8)),
    (⟨[(1, 4)], [(1, 2)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 18))] : SOS.Polynomial) =
    [(⟨[(0, 2)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 4 0)),
    (⟨[(0, 3)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 4 1)),
    (⟨[(0, 3)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 4 2)),
    (⟨[(0, 4)], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 4 3)),
    (⟨[(1, 2)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 4 4)),
    (⟨[(1, 3)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 4 5)),
    (⟨[(1, 3)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 4 6)),
    (⟨[(1, 4)], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 4 7))]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, phase_zero_eval, mul_one]

end
end CGLMP5.SOSFinite
