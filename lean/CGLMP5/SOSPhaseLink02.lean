import CGLMP5.SOSCompressedCheck02
import CGLMP5.SOSPhaseLinkBase

namespace CGLMP5.SOSFinite
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
lemma source_phase_polynomial_2
(hmul : ∀ a b : Scalar, Scalar.eval (Scalar.mul a b) = Scalar.eval a * Scalar.eval b) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore 2 c)))
      (fun p => Scalar.eval (phase p)) (localTerms 2) =
      (CanonicalData.polynomial 2).map (fun t => (t.1, Scalar.eval t.2)) := by
  have h0 := congrArg Scalar.eval (funext source_phase_2_0)
  have h1 := congrArg Scalar.eval (funext source_phase_2_1)
  have h2 := congrArg Scalar.eval (funext source_phase_2_2)
  have h3 := congrArg Scalar.eval (funext source_phase_2_3)
  have h4 := congrArg Scalar.eval (funext source_phase_2_4)
  have h5 := congrArg Scalar.eval (funext source_phase_2_5)
  have h6 := congrArg Scalar.eval (funext source_phase_2_6)
  have h7 := congrArg Scalar.eval (funext source_phase_2_7)
  have h8 := congrArg Scalar.eval (funext source_phase_2_8)
  have h9 := congrArg Scalar.eval (funext source_phase_2_9)
  have h10 := congrArg Scalar.eval (funext source_phase_2_10)
  have h11 := congrArg Scalar.eval (funext source_phase_2_11)
  have h12 := congrArg Scalar.eval (funext source_phase_2_12)
  have h13 := congrArg Scalar.eval (funext source_phase_2_13)
  have h14 := congrArg Scalar.eval (funext source_phase_2_14)
  have h15 := congrArg Scalar.eval (funext source_phase_2_15)
  simp only [hmul] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  change ([(⟨[], [(0, 1)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 0)),
    (⟨[], [(1, 1)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 8)),
    (⟨[(0, 1)], []⟩, Scalar.eval (core 2) * Scalar.eval (phase 6)),
    (⟨[(0, 2)], [(0, 4)]⟩, Scalar.eval (core 6) * Scalar.eval (phase 0)),
    (⟨[(0, 2)], [(1, 4)]⟩, Scalar.eval (core 7) * Scalar.eval (phase 0)),
    (⟨[(0, 3)], [(0, 3)]⟩, Scalar.eval (core 8) * Scalar.eval (phase 0)),
    (⟨[(0, 3)], [(1, 3)]⟩, Scalar.eval (core 8) * Scalar.eval (phase 14)),
    (⟨[(0, 4)], [(0, 2)]⟩, Scalar.eval (core 7) * Scalar.eval (phase 10)),
    (⟨[(0, 4)], [(1, 2)]⟩, Scalar.eval (core 6) * Scalar.eval (phase 18)),
    (⟨[(1, 1)], []⟩, Scalar.eval (core 2) * Scalar.eval (phase 14)),
    (⟨[(1, 2)], [(0, 4)]⟩, Scalar.eval (core 7) * Scalar.eval (phase 4)),
    (⟨[(1, 2)], [(1, 4)]⟩, Scalar.eval (core 6) * Scalar.eval (phase 8)),
    (⟨[(1, 3)], [(0, 3)]⟩, Scalar.eval (core 8) * Scalar.eval (phase 14)),
    (⟨[(1, 3)], [(1, 3)]⟩, Scalar.eval (core 8) * Scalar.eval (phase 8)),
    (⟨[(1, 4)], [(0, 2)]⟩, Scalar.eval (core 6) * Scalar.eval (phase 14)),
    (⟨[(1, 4)], [(1, 2)]⟩, Scalar.eval (core 7) * Scalar.eval (phase 18))] : SOS.Polynomial) =
    [(⟨[], [(0, 1)]⟩, Scalar.eval (canonicalCoefficient 2 0)),
    (⟨[], [(1, 1)]⟩, Scalar.eval (canonicalCoefficient 2 1)),
    (⟨[(0, 1)], []⟩, Scalar.eval (canonicalCoefficient 2 2)),
    (⟨[(0, 2)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 2 3)),
    (⟨[(0, 2)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 2 4)),
    (⟨[(0, 3)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 2 5)),
    (⟨[(0, 3)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 2 6)),
    (⟨[(0, 4)], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 2 7)),
    (⟨[(0, 4)], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 2 8)),
    (⟨[(1, 1)], []⟩, Scalar.eval (canonicalCoefficient 2 9)),
    (⟨[(1, 2)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 2 10)),
    (⟨[(1, 2)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 2 11)),
    (⟨[(1, 3)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 2 12)),
    (⟨[(1, 3)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 2 13)),
    (⟨[(1, 4)], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 2 14)),
    (⟨[(1, 4)], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 2 15))]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, phase_zero_eval, mul_one]

end
end CGLMP5.SOSFinite
