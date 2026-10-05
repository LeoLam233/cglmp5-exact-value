import CGLMP5.SOSCompressedCheck13
import CGLMP5.SOSPhaseLinkBase

namespace CGLMP5.SOSFinite
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
lemma source_phase_polynomial_13
(hmul : ∀ a b : Scalar, Scalar.eval (Scalar.mul a b) = Scalar.eval a * Scalar.eval b) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore 13 c)))
      (fun p => Scalar.eval (phase p)) (localTerms 13) =
      (CanonicalData.polynomial 13).map (fun t => (t.1, Scalar.eval t.2)) := by
  have h0 := congrArg Scalar.eval (funext source_phase_13_0)
  have h1 := congrArg Scalar.eval (funext source_phase_13_1)
  have h2 := congrArg Scalar.eval (funext source_phase_13_2)
  have h3 := congrArg Scalar.eval (funext source_phase_13_3)
  have h4 := congrArg Scalar.eval (funext source_phase_13_4)
  have h5 := congrArg Scalar.eval (funext source_phase_13_5)
  have h6 := congrArg Scalar.eval (funext source_phase_13_6)
  have h7 := congrArg Scalar.eval (funext source_phase_13_7)
  have h8 := congrArg Scalar.eval (funext source_phase_13_8)
  have h9 := congrArg Scalar.eval (funext source_phase_13_9)
  have h10 := congrArg Scalar.eval (funext source_phase_13_10)
  have h11 := congrArg Scalar.eval (funext source_phase_13_11)
  simp only [hmul] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  change ([(⟨[], [(0, 4)]⟩, Scalar.eval (core 26) * Scalar.eval (phase 0)),
    (⟨[], [(1, 4)]⟩, Scalar.eval (core 26) * Scalar.eval (phase 2)),
    (⟨[(0, 1)], [(0, 3)]⟩, Scalar.eval (core 27) * Scalar.eval (phase 0)),
    (⟨[(0, 2)], [(0, 2)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 0)),
    (⟨[(0, 2)], [(1, 2)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 1)),
    (⟨[(0, 3)], [(1, 1)]⟩, Scalar.eval (core 27) * Scalar.eval (phase 5)),
    (⟨[(0, 4)], []⟩, Scalar.eval (core 26) * Scalar.eval (phase 9)),
    (⟨[(1, 1)], [(1, 3)]⟩, Scalar.eval (core 27) * Scalar.eval (phase 2)),
    (⟨[(1, 2)], [(0, 2)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 11)),
    (⟨[(1, 2)], [(1, 2)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 2)),
    (⟨[(1, 3)], [(0, 1)]⟩, Scalar.eval (core 27) * Scalar.eval (phase 11)),
    (⟨[(1, 4)], []⟩, Scalar.eval (core 26) * Scalar.eval (phase 11))] : SOS.Polynomial) =
    [(⟨[], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 13 0)),
    (⟨[], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 13 1)),
    (⟨[(0, 1)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 13 2)),
    (⟨[(0, 2)], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 13 3)),
    (⟨[(0, 2)], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 13 4)),
    (⟨[(0, 3)], [(1, 1)]⟩, Scalar.eval (canonicalCoefficient 13 5)),
    (⟨[(0, 4)], []⟩, Scalar.eval (canonicalCoefficient 13 6)),
    (⟨[(1, 1)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 13 7)),
    (⟨[(1, 2)], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 13 8)),
    (⟨[(1, 2)], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 13 9)),
    (⟨[(1, 3)], [(0, 1)]⟩, Scalar.eval (canonicalCoefficient 13 10)),
    (⟨[(1, 4)], []⟩, Scalar.eval (canonicalCoefficient 13 11))]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, phase_zero_eval, mul_one]

end
end CGLMP5.SOSFinite
