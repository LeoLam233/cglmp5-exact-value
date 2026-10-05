import CGLMP5.SOSCompressedCheck03
import CGLMP5.SOSPhaseLinkBase

namespace CGLMP5.SOSFinite
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
lemma source_phase_polynomial_3
(hmul : ∀ a b : Scalar, Scalar.eval (Scalar.mul a b) = Scalar.eval a * Scalar.eval b) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore 3 c)))
      (fun p => Scalar.eval (phase p)) (localTerms 3) =
      (CanonicalData.polynomial 3).map (fun t => (t.1, Scalar.eval t.2)) := by
  have h0 := congrArg Scalar.eval (funext source_phase_3_0)
  have h1 := congrArg Scalar.eval (funext source_phase_3_1)
  have h2 := congrArg Scalar.eval (funext source_phase_3_2)
  have h3 := congrArg Scalar.eval (funext source_phase_3_3)
  have h4 := congrArg Scalar.eval (funext source_phase_3_4)
  have h5 := congrArg Scalar.eval (funext source_phase_3_5)
  have h6 := congrArg Scalar.eval (funext source_phase_3_6)
  have h7 := congrArg Scalar.eval (funext source_phase_3_7)
  have h8 := congrArg Scalar.eval (funext source_phase_3_8)
  have h9 := congrArg Scalar.eval (funext source_phase_3_9)
  have h10 := congrArg Scalar.eval (funext source_phase_3_10)
  have h11 := congrArg Scalar.eval (funext source_phase_3_11)
  simp only [hmul] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  change ([(⟨[(0, 2)], [(0, 4)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 0)),
    (⟨[(0, 2)], [(1, 4)]⟩, Scalar.eval (core 9) * Scalar.eval (phase 0)),
    (⟨[(0, 3)], [(0, 3)]⟩, Scalar.eval (core 10) * Scalar.eval (phase 0)),
    (⟨[(0, 3)], [(1, 3)]⟩, Scalar.eval (core 10) * Scalar.eval (phase 14)),
    (⟨[(0, 4)], [(0, 2)]⟩, Scalar.eval (core 9) * Scalar.eval (phase 10)),
    (⟨[(0, 4)], [(1, 2)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 18)),
    (⟨[(1, 2)], [(0, 4)]⟩, Scalar.eval (core 9) * Scalar.eval (phase 4)),
    (⟨[(1, 2)], [(1, 4)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 8)),
    (⟨[(1, 3)], [(0, 3)]⟩, Scalar.eval (core 10) * Scalar.eval (phase 14)),
    (⟨[(1, 3)], [(1, 3)]⟩, Scalar.eval (core 10) * Scalar.eval (phase 8)),
    (⟨[(1, 4)], [(0, 2)]⟩, Scalar.eval (core 2) * Scalar.eval (phase 14)),
    (⟨[(1, 4)], [(1, 2)]⟩, Scalar.eval (core 9) * Scalar.eval (phase 18))] : SOS.Polynomial) =
    [(⟨[(0, 2)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 3 0)),
    (⟨[(0, 2)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 3 1)),
    (⟨[(0, 3)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 3 2)),
    (⟨[(0, 3)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 3 3)),
    (⟨[(0, 4)], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 3 4)),
    (⟨[(0, 4)], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 3 5)),
    (⟨[(1, 2)], [(0, 4)]⟩, Scalar.eval (canonicalCoefficient 3 6)),
    (⟨[(1, 2)], [(1, 4)]⟩, Scalar.eval (canonicalCoefficient 3 7)),
    (⟨[(1, 3)], [(0, 3)]⟩, Scalar.eval (canonicalCoefficient 3 8)),
    (⟨[(1, 3)], [(1, 3)]⟩, Scalar.eval (canonicalCoefficient 3 9)),
    (⟨[(1, 4)], [(0, 2)]⟩, Scalar.eval (canonicalCoefficient 3 10)),
    (⟨[(1, 4)], [(1, 2)]⟩, Scalar.eval (canonicalCoefficient 3 11))]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, phase_zero_eval, mul_one]

end
end CGLMP5.SOSFinite
