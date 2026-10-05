import CGLMP5.SOSCompressedCheck12
import CGLMP5.SOSPhaseLinkBase

namespace CGLMP5.SOSFinite
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
lemma source_phase_polynomial_12
(hmul : ∀ a b : Scalar, Scalar.eval (Scalar.mul a b) = Scalar.eval a * Scalar.eval b) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore 12 c)))
      (fun p => Scalar.eval (phase p)) (localTerms 12) =
      (CanonicalData.polynomial 12).map (fun t => (t.1, Scalar.eval t.2)) := by
  have h0 := congrArg Scalar.eval (funext source_phase_12_0)
  have h1 := congrArg Scalar.eval (funext source_phase_12_1)
  have h2 := congrArg Scalar.eval (funext source_phase_12_2)
  have h3 := congrArg Scalar.eval (funext source_phase_12_3)
  have h4 := congrArg Scalar.eval (funext source_phase_12_4)
  have h5 := congrArg Scalar.eval (funext source_phase_12_5)
  have h6 := congrArg Scalar.eval (funext source_phase_12_6)
  have h7 := congrArg Scalar.eval (funext source_phase_12_7)
  have h8 := congrArg Scalar.eval (funext source_phase_12_8)
  have h9 := congrArg Scalar.eval (funext source_phase_12_9)
  have h10 := congrArg Scalar.eval (funext source_phase_12_10)
  have h11 := congrArg Scalar.eval (funext source_phase_12_11)
  have h12 := congrArg Scalar.eval (funext source_phase_12_12)
  have h13 := congrArg Scalar.eval (funext source_phase_12_13)
  have h14 := congrArg Scalar.eval (funext source_phase_12_14)
  have h15 := congrArg Scalar.eval (funext source_phase_12_15)
  simp only [hmul] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  change ([(⟨[], [(0, 4)]⟩, Scalar.eval (core 23) * Scalar.eval (phase 0)),
    (⟨[], [(1, 4)]⟩, Scalar.eval (core 23) * Scalar.eval (phase 2)),
    (⟨[(0, 1)], [(0, 3)]⟩, Scalar.eval (core 24) * Scalar.eval (phase 0)),
    (⟨[(0, 1)], [(1, 3)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 0)),
    (⟨[(0, 2)], [(0, 2)]⟩, Scalar.eval (core 25) * Scalar.eval (phase 0)),
    (⟨[(0, 2)], [(1, 2)]⟩, Scalar.eval (core 25) * Scalar.eval (phase 1)),
    (⟨[(0, 3)], [(0, 1)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 3)),
    (⟨[(0, 3)], [(1, 1)]⟩, Scalar.eval (core 24) * Scalar.eval (phase 5)),
    (⟨[(0, 4)], []⟩, Scalar.eval (core 23) * Scalar.eval (phase 9)),
    (⟨[(1, 1)], [(0, 3)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 14)),
    (⟨[(1, 1)], [(1, 3)]⟩, Scalar.eval (core 24) * Scalar.eval (phase 2)),
    (⟨[(1, 2)], [(0, 2)]⟩, Scalar.eval (core 25) * Scalar.eval (phase 11)),
    (⟨[(1, 2)], [(1, 2)]⟩, Scalar.eval (core 25) * Scalar.eval (phase 2)),
    (⟨[(1, 3)], [(0, 1)]⟩, Scalar.eval (core 24) * Scalar.eval (phase 11)),
    (⟨[(1, 3)], [(1, 1)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 5)),
    (⟨[(1, 4)], []⟩, Scalar.eval (core 23) * Scalar.eval (phase 11))] : SOS.Polynomial) =
    [(⟨[], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 12 0)),
    (⟨[], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 12 1)),
    (⟨[(0, 1)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 12 2)),
    (⟨[(0, 1)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 12 3)),
    (⟨[(0, 2)], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 12 4)),
    (⟨[(0, 2)], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 12 5)),
    (⟨[(0, 3)], [(0, 1)]⟩, Scalar.eval (canonicalCoefficient 12 6)),
    (⟨[(0, 3)], [(1, 1)]⟩, Scalar.eval (canonicalCoefficient 12 7)),
    (⟨[(0, 4)], []⟩, Scalar.eval (canonicalCoefficient 12 8)),
    (⟨[(1, 1)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 12 9)),
    (⟨[(1, 1)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 12 10)),
    (⟨[(1, 2)], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 12 11)),
    (⟨[(1, 2)], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 12 12)),
    (⟨[(1, 3)], [(0, 1)]⟩, Scalar.eval (canonicalCoefficient 12 13)),
    (⟨[(1, 3)], [(1, 1)]⟩, Scalar.eval (canonicalCoefficient 12 14)),
    (⟨[(1, 4)], []⟩, Scalar.eval (canonicalCoefficient 12 15))]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, phase_zero_eval, mul_one]

end
end CGLMP5.SOSFinite
