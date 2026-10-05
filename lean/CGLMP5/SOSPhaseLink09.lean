import CGLMP5.SOSCompressedCheck09
import CGLMP5.SOSPhaseLinkBase

namespace CGLMP5.SOSFinite
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
lemma source_phase_polynomial_9
(hmul : ∀ a b : Scalar, Scalar.eval (Scalar.mul a b) = Scalar.eval a * Scalar.eval b) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore 9 c)))
      (fun p => Scalar.eval (phase p)) (localTerms 9) =
      (CanonicalData.polynomial 9).map (fun t => (t.1, Scalar.eval t.2)) := by
  have h0 := congrArg Scalar.eval (funext source_phase_9_0)
  have h1 := congrArg Scalar.eval (funext source_phase_9_1)
  have h2 := congrArg Scalar.eval (funext source_phase_9_2)
  have h3 := congrArg Scalar.eval (funext source_phase_9_3)
  have h4 := congrArg Scalar.eval (funext source_phase_9_4)
  have h5 := congrArg Scalar.eval (funext source_phase_9_5)
  have h6 := congrArg Scalar.eval (funext source_phase_9_6)
  have h7 := congrArg Scalar.eval (funext source_phase_9_7)
  have h8 := congrArg Scalar.eval (funext source_phase_9_8)
  have h9 := congrArg Scalar.eval (funext source_phase_9_9)
  have h10 := congrArg Scalar.eval (funext source_phase_9_10)
  have h11 := congrArg Scalar.eval (funext source_phase_9_11)
  have h12 := congrArg Scalar.eval (funext source_phase_9_12)
  have h13 := congrArg Scalar.eval (funext source_phase_9_13)
  have h14 := congrArg Scalar.eval (funext source_phase_9_14)
  have h15 := congrArg Scalar.eval (funext source_phase_9_15)
  simp only [hmul] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  change ([(⟨[], [(0, 3)]⟩, Scalar.eval (core 18) * Scalar.eval (phase 0)),
    (⟨[], [(1, 3)]⟩, Scalar.eval (core 18) * Scalar.eval (phase 4)),
    (⟨[(0, 1)], [(0, 2)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 0)),
    (⟨[(0, 1)], [(1, 2)]⟩, Scalar.eval (core 19) * Scalar.eval (phase 0)),
    (⟨[(0, 2)], [(0, 1)]⟩, Scalar.eval (core 19) * Scalar.eval (phase 0)),
    (⟨[(0, 2)], [(1, 1)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 4)),
    (⟨[(0, 3)], []⟩, Scalar.eval (core 18) * Scalar.eval (phase 8)),
    (⟨[(0, 4)], [(0, 4)]⟩, Scalar.eval (core 20) * Scalar.eval (phase 0)),
    (⟨[(0, 4)], [(1, 4)]⟩, Scalar.eval (core 20) * Scalar.eval (phase 12)),
    (⟨[(1, 1)], [(0, 2)]⟩, Scalar.eval (core 19) * Scalar.eval (phase 12)),
    (⟨[(1, 1)], [(1, 2)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 4)),
    (⟨[(1, 2)], [(0, 1)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 12)),
    (⟨[(1, 2)], [(1, 1)]⟩, Scalar.eval (core 19) * Scalar.eval (phase 4)),
    (⟨[(1, 3)], []⟩, Scalar.eval (core 18) * Scalar.eval (phase 12)),
    (⟨[(1, 4)], [(0, 4)]⟩, Scalar.eval (core 20) * Scalar.eval (phase 12)),
    (⟨[(1, 4)], [(1, 4)]⟩, Scalar.eval (core 20) * Scalar.eval (phase 4))] : SOS.Polynomial) =
    [(⟨[], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 9 0)),
    (⟨[], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 9 1)),
    (⟨[(0, 1)], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 9 2)),
    (⟨[(0, 1)], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 9 3)),
    (⟨[(0, 2)], [(0, 1)]⟩, Scalar.eval (canonicalCoefficient 9 4)),
    (⟨[(0, 2)], [(1, 1)]⟩, Scalar.eval (canonicalCoefficient 9 5)),
    (⟨[(0, 3)], []⟩, Scalar.eval (canonicalCoefficient 9 6)),
    (⟨[(0, 4)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 9 7)),
    (⟨[(0, 4)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 9 8)),
    (⟨[(1, 1)], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 9 9)),
    (⟨[(1, 1)], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 9 10)),
    (⟨[(1, 2)], [(0, 1)]⟩, Scalar.eval (canonicalCoefficient 9 11)),
    (⟨[(1, 2)], [(1, 1)]⟩, Scalar.eval (canonicalCoefficient 9 12)),
    (⟨[(1, 3)], []⟩, Scalar.eval (canonicalCoefficient 9 13)),
    (⟨[(1, 4)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 9 14)),
    (⟨[(1, 4)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 9 15))]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, phase_zero_eval, mul_one]

end
end CGLMP5.SOSFinite
