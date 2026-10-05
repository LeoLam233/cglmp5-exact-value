import CGLMP5.SOSCompressedCheck06
import CGLMP5.SOSPhaseLinkBase

namespace CGLMP5.SOSFinite
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
lemma source_phase_polynomial_6
(hmul : ∀ a b : Scalar, Scalar.eval (Scalar.mul a b) = Scalar.eval a * Scalar.eval b) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore 6 c)))
      (fun p => Scalar.eval (phase p)) (localTerms 6) =
      (CanonicalData.polynomial 6).map (fun t => (t.1, Scalar.eval t.2)) := by
  have h0 := congrArg Scalar.eval (funext source_phase_6_0)
  have h1 := congrArg Scalar.eval (funext source_phase_6_1)
  have h2 := congrArg Scalar.eval (funext source_phase_6_2)
  have h3 := congrArg Scalar.eval (funext source_phase_6_3)
  have h4 := congrArg Scalar.eval (funext source_phase_6_4)
  have h5 := congrArg Scalar.eval (funext source_phase_6_5)
  have h6 := congrArg Scalar.eval (funext source_phase_6_6)
  have h7 := congrArg Scalar.eval (funext source_phase_6_7)
  have h8 := congrArg Scalar.eval (funext source_phase_6_8)
  have h9 := congrArg Scalar.eval (funext source_phase_6_9)
  have h10 := congrArg Scalar.eval (funext source_phase_6_10)
  have h11 := congrArg Scalar.eval (funext source_phase_6_11)
  have h12 := congrArg Scalar.eval (funext source_phase_6_12)
  have h13 := congrArg Scalar.eval (funext source_phase_6_13)
  have h14 := congrArg Scalar.eval (funext source_phase_6_14)
  have h15 := congrArg Scalar.eval (funext source_phase_6_15)
  simp only [hmul] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  change ([(⟨[], [(0, 2)]⟩, Scalar.eval (core 12) * Scalar.eval (phase 0)),
    (⟨[], [(1, 2)]⟩, Scalar.eval (core 12) * Scalar.eval (phase 6)),
    (⟨[(0, 1)], [(0, 1)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 0)),
    (⟨[(0, 1)], [(1, 1)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 3)),
    (⟨[(0, 2)], []⟩, Scalar.eval (core 12) * Scalar.eval (phase 7)),
    (⟨[(0, 3)], [(0, 4)]⟩, Scalar.eval (core 13) * Scalar.eval (phase 0)),
    (⟨[(0, 3)], [(1, 4)]⟩, Scalar.eval (core 14) * Scalar.eval (phase 0)),
    (⟨[(0, 4)], [(0, 3)]⟩, Scalar.eval (core 14) * Scalar.eval (phase 9)),
    (⟨[(0, 4)], [(1, 3)]⟩, Scalar.eval (core 13) * Scalar.eval (phase 15)),
    (⟨[(1, 1)], [(0, 1)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 13)),
    (⟨[(1, 1)], [(1, 1)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 6)),
    (⟨[(1, 2)], []⟩, Scalar.eval (core 12) * Scalar.eval (phase 13)),
    (⟨[(1, 3)], [(0, 4)]⟩, Scalar.eval (core 14) * Scalar.eval (phase 2)),
    (⟨[(1, 3)], [(1, 4)]⟩, Scalar.eval (core 13) * Scalar.eval (phase 6)),
    (⟨[(1, 4)], [(0, 3)]⟩, Scalar.eval (core 13) * Scalar.eval (phase 13)),
    (⟨[(1, 4)], [(1, 3)]⟩, Scalar.eval (core 14) * Scalar.eval (phase 15))] : SOS.Polynomial) =
    [(⟨[], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 6 0)),
    (⟨[], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 6 1)),
    (⟨[(0, 1)], [(0, 1)]⟩, Scalar.eval (canonicalCoefficient 6 2)),
    (⟨[(0, 1)], [(1, 1)]⟩, Scalar.eval (canonicalCoefficient 6 3)),
    (⟨[(0, 2)], []⟩, Scalar.eval (canonicalCoefficient 6 4)),
    (⟨[(0, 3)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 6 5)),
    (⟨[(0, 3)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 6 6)),
    (⟨[(0, 4)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 6 7)),
    (⟨[(0, 4)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 6 8)),
    (⟨[(1, 1)], [(0, 1)]⟩, Scalar.eval (canonicalCoefficient 6 9)),
    (⟨[(1, 1)], [(1, 1)]⟩, Scalar.eval (canonicalCoefficient 6 10)),
    (⟨[(1, 2)], []⟩, Scalar.eval (canonicalCoefficient 6 11)),
    (⟨[(1, 3)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 6 12)),
    (⟨[(1, 3)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 6 13)),
    (⟨[(1, 4)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 6 14)),
    (⟨[(1, 4)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 6 15))]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, phase_zero_eval, mul_one]

end
end CGLMP5.SOSFinite
