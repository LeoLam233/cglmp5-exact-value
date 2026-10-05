import CGLMP5.SOSCompressedCheck01
import CGLMP5.SOSPhaseLinkBase

namespace CGLMP5.SOSFinite
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
lemma source_phase_polynomial_1
(hmul : ∀ a b : Scalar, Scalar.eval (Scalar.mul a b) = Scalar.eval a * Scalar.eval b) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore 1 c)))
      (fun p => Scalar.eval (phase p)) (localTerms 1) =
      (CanonicalData.polynomial 1).map (fun t => (t.1, Scalar.eval t.2)) := by
  have h0 := congrArg Scalar.eval (funext source_phase_1_0)
  have h1 := congrArg Scalar.eval (funext source_phase_1_1)
  have h2 := congrArg Scalar.eval (funext source_phase_1_2)
  have h3 := congrArg Scalar.eval (funext source_phase_1_3)
  have h4 := congrArg Scalar.eval (funext source_phase_1_4)
  have h5 := congrArg Scalar.eval (funext source_phase_1_5)
  have h6 := congrArg Scalar.eval (funext source_phase_1_6)
  have h7 := congrArg Scalar.eval (funext source_phase_1_7)
  have h8 := congrArg Scalar.eval (funext source_phase_1_8)
  have h9 := congrArg Scalar.eval (funext source_phase_1_9)
  have h10 := congrArg Scalar.eval (funext source_phase_1_10)
  have h11 := congrArg Scalar.eval (funext source_phase_1_11)
  simp only [hmul] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  change ([(⟨[], [(0, 1)]⟩, Scalar.eval (core 4) * Scalar.eval (phase 0)),
    (⟨[], [(1, 1)]⟩, Scalar.eval (core 4) * Scalar.eval (phase 18)),
    (⟨[(0, 1)], []⟩, Scalar.eval (core 4) * Scalar.eval (phase 1)),
    (⟨[(0, 2)], [(0, 4)]⟩, Scalar.eval (core 5) * Scalar.eval (phase 0)),
    (⟨[(0, 3)], [(0, 3)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 0)),
    (⟨[(0, 3)], [(1, 3)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 9)),
    (⟨[(0, 4)], [(1, 2)]⟩, Scalar.eval (core 5) * Scalar.eval (phase 13)),
    (⟨[(1, 1)], []⟩, Scalar.eval (core 4) * Scalar.eval (phase 19)),
    (⟨[(1, 2)], [(1, 4)]⟩, Scalar.eval (core 5) * Scalar.eval (phase 18)),
    (⟨[(1, 3)], [(0, 3)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 19)),
    (⟨[(1, 3)], [(1, 3)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 18)),
    (⟨[(1, 4)], [(0, 2)]⟩, Scalar.eval (core 5) * Scalar.eval (phase 19))] : SOS.Polynomial) =
    [(⟨[], [(0, 1)]⟩, Scalar.eval (canonicalCoefficient 1 0)),
    (⟨[], [(1, 1)]⟩, Scalar.eval (canonicalCoefficient 1 1)),
    (⟨[(0, 1)], []⟩, Scalar.eval (canonicalCoefficient 1 2)),
    (⟨[(0, 2)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 1 3)),
    (⟨[(0, 3)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 1 4)),
    (⟨[(0, 3)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 1 5)),
    (⟨[(0, 4)], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 1 6)),
    (⟨[(1, 1)], []⟩, Scalar.eval (canonicalCoefficient 1 7)),
    (⟨[(1, 2)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 1 8)),
    (⟨[(1, 3)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 1 9)),
    (⟨[(1, 3)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 1 10)),
    (⟨[(1, 4)], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 1 11))]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, phase_zero_eval, mul_one]

end
end CGLMP5.SOSFinite
