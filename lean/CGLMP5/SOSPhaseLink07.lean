import CGLMP5.SOSCompressedCheck07
import CGLMP5.SOSPhaseLinkBase

namespace CGLMP5.SOSFinite
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
lemma source_phase_polynomial_7
(hmul : ∀ a b : Scalar, Scalar.eval (Scalar.mul a b) = Scalar.eval a * Scalar.eval b) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore 7 c)))
      (fun p => Scalar.eval (phase p)) (localTerms 7) =
      (CanonicalData.polynomial 7).map (fun t => (t.1, Scalar.eval t.2)) := by
  have h0 := congrArg Scalar.eval (funext source_phase_7_0)
  have h1 := congrArg Scalar.eval (funext source_phase_7_1)
  have h2 := congrArg Scalar.eval (funext source_phase_7_2)
  have h3 := congrArg Scalar.eval (funext source_phase_7_3)
  have h4 := congrArg Scalar.eval (funext source_phase_7_4)
  have h5 := congrArg Scalar.eval (funext source_phase_7_5)
  have h6 := congrArg Scalar.eval (funext source_phase_7_6)
  have h7 := congrArg Scalar.eval (funext source_phase_7_7)
  have h8 := congrArg Scalar.eval (funext source_phase_7_8)
  have h9 := congrArg Scalar.eval (funext source_phase_7_9)
  have h10 := congrArg Scalar.eval (funext source_phase_7_10)
  have h11 := congrArg Scalar.eval (funext source_phase_7_11)
  simp only [hmul] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  change ([(⟨[], [(0, 2)]⟩, Scalar.eval (core 15) * Scalar.eval (phase 0)),
    (⟨[], [(1, 2)]⟩, Scalar.eval (core 15) * Scalar.eval (phase 6)),
    (⟨[(0, 2)], []⟩, Scalar.eval (core 15) * Scalar.eval (phase 7)),
    (⟨[(0, 3)], [(0, 4)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 0)),
    (⟨[(0, 3)], [(1, 4)]⟩, Scalar.eval (core 16) * Scalar.eval (phase 0)),
    (⟨[(0, 4)], [(0, 3)]⟩, Scalar.eval (core 16) * Scalar.eval (phase 9)),
    (⟨[(0, 4)], [(1, 3)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 15)),
    (⟨[(1, 2)], []⟩, Scalar.eval (core 15) * Scalar.eval (phase 13)),
    (⟨[(1, 3)], [(0, 4)]⟩, Scalar.eval (core 16) * Scalar.eval (phase 2)),
    (⟨[(1, 3)], [(1, 4)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 6)),
    (⟨[(1, 4)], [(0, 3)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 13)),
    (⟨[(1, 4)], [(1, 3)]⟩, Scalar.eval (core 16) * Scalar.eval (phase 15))] : SOS.Polynomial) =
    [(⟨[], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 7 0)),
    (⟨[], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 7 1)),
    (⟨[(0, 2)], []⟩, Scalar.eval (canonicalCoefficient 7 2)),
    (⟨[(0, 3)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 7 3)),
    (⟨[(0, 3)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 7 4)),
    (⟨[(0, 4)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 7 5)),
    (⟨[(0, 4)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 7 6)),
    (⟨[(1, 2)], []⟩, Scalar.eval (canonicalCoefficient 7 7)),
    (⟨[(1, 3)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 7 8)),
    (⟨[(1, 3)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 7 9)),
    (⟨[(1, 4)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 7 10)),
    (⟨[(1, 4)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 7 11))]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, phase_zero_eval, mul_one]

end
end CGLMP5.SOSFinite
