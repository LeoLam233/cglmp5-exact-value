import CGLMP5.SOSCompressedCheck00
import CGLMP5.SOSPhaseLinkBase

namespace CGLMP5.SOSFinite
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
lemma source_phase_polynomial_0
(hmul : ∀ a b : Scalar, Scalar.eval (Scalar.mul a b) = Scalar.eval a * Scalar.eval b) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore 0 c)))
      (fun p => Scalar.eval (phase p)) (localTerms 0) =
      (CanonicalData.polynomial 0).map (fun t => (t.1, Scalar.eval t.2)) := by
  have h0 := congrArg Scalar.eval (funext source_phase_0_0)
  have h1 := congrArg Scalar.eval (funext source_phase_0_1)
  have h2 := congrArg Scalar.eval (funext source_phase_0_2)
  have h3 := congrArg Scalar.eval (funext source_phase_0_3)
  have h4 := congrArg Scalar.eval (funext source_phase_0_4)
  have h5 := congrArg Scalar.eval (funext source_phase_0_5)
  have h6 := congrArg Scalar.eval (funext source_phase_0_6)
  have h7 := congrArg Scalar.eval (funext source_phase_0_7)
  have h8 := congrArg Scalar.eval (funext source_phase_0_8)
  have h9 := congrArg Scalar.eval (funext source_phase_0_9)
  have h10 := congrArg Scalar.eval (funext source_phase_0_10)
  have h11 := congrArg Scalar.eval (funext source_phase_0_11)
  have h12 := congrArg Scalar.eval (funext source_phase_0_12)
  have h13 := congrArg Scalar.eval (funext source_phase_0_13)
  have h14 := congrArg Scalar.eval (funext source_phase_0_14)
  have h15 := congrArg Scalar.eval (funext source_phase_0_15)
  simp only [hmul] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  change ([(⟨[], [(0, 1)]⟩, Scalar.eval (core 0) * Scalar.eval (phase 0)),
    (⟨[], [(1, 1)]⟩, Scalar.eval (core 0) * Scalar.eval (phase 18)),
    (⟨[(0, 1)], []⟩, Scalar.eval (core 0) * Scalar.eval (phase 1)),
    (⟨[(0, 2)], [(0, 4)]⟩, Scalar.eval (core 1) * Scalar.eval (phase 0)),
    (⟨[(0, 2)], [(1, 4)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 0)),
    (⟨[(0, 3)], [(0, 3)]⟩, Scalar.eval (core 3) * Scalar.eval (phase 0)),
    (⟨[(0, 3)], [(1, 3)]⟩, Scalar.eval (core 3) * Scalar.eval (phase 9)),
    (⟨[(0, 4)], [(0, 2)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 15)),
    (⟨[(0, 4)], [(1, 2)]⟩, Scalar.eval (core 1) * Scalar.eval (phase 13)),
    (⟨[(1, 1)], []⟩, Scalar.eval (core 0) * Scalar.eval (phase 19)),
    (⟨[(1, 2)], [(0, 4)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 14)),
    (⟨[(1, 2)], [(1, 4)]⟩, Scalar.eval (core 1) * Scalar.eval (phase 18)),
    (⟨[(1, 3)], [(0, 3)]⟩, Scalar.eval (core 3) * Scalar.eval (phase 19)),
    (⟨[(1, 3)], [(1, 3)]⟩, Scalar.eval (core 3) * Scalar.eval (phase 18)),
    (⟨[(1, 4)], [(0, 2)]⟩, Scalar.eval (core 1) * Scalar.eval (phase 19)),
    (⟨[(1, 4)], [(1, 2)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 13))] : SOS.Polynomial) =
    [(⟨[], [(0, 1)]⟩, Scalar.eval (canonicalCoefficient 0 0)),
    (⟨[], [(1, 1)]⟩, Scalar.eval (canonicalCoefficient 0 1)),
    (⟨[(0, 1)], []⟩, Scalar.eval (canonicalCoefficient 0 2)),
    (⟨[(0, 2)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 0 3)),
    (⟨[(0, 2)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 0 4)),
    (⟨[(0, 3)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 0 5)),
    (⟨[(0, 3)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 0 6)),
    (⟨[(0, 4)], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 0 7)),
    (⟨[(0, 4)], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 0 8)),
    (⟨[(1, 1)], []⟩, Scalar.eval (canonicalCoefficient 0 9)),
    (⟨[(1, 2)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 0 10)),
    (⟨[(1, 2)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 0 11)),
    (⟨[(1, 3)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 0 12)),
    (⟨[(1, 3)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 0 13)),
    (⟨[(1, 4)], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 0 14)),
    (⟨[(1, 4)], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 0 15))]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, phase_zero_eval, mul_one]

end
end CGLMP5.SOSFinite
