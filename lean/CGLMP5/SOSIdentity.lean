import CGLMP5.SOSReflection
import CGLMP5.SOSSemantics
import CGLMP5.SOSTarget

/-!
# The canonical fourteen-term exact operator identity

All arithmetic is discharged by the imported integer-coordinate certificates.
All word and scalar reductions are interpreted by proved evaluation lemmas.
No same-party commutation or finite-dimensionality premise is present.
-/
namespace CGLMP5.SOS
noncomputable section

/-- The compact exact CGLMP5 SOS identity in every complex star-algebra representation. -/
theorem compact_identity {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    (a b : Fin 2 → unitary R)
    (ha : ∀ i, a i ^ 5 = 1) (hb : ∀ i, b i ^ 5 = 1)
    (hab : ∀ i j, Commute (a i) (b j)) :
    (mu : ℂ) • (1 : R) - bell (zeta ^ 4) a b =
      ∑ j : Fin 14, (weightValue j : ℂ) •
        (star (realizingPolynomial a b j) * realizingPolynomial a b j +
          realizingPolynomial a b j * star (realizingPolynomial a b j)) := by
  calc
    (mu : ℂ) • (1 : R) - bell (zeta ^ 4) a b =
        evaluate a b (SOSFinite.complexPolynomial SOSFinite.targetPolynomial) := by
      simpa only [SOSFinite.complexPolynomial] using (SOSFinite.target_evaluation a b).symm
    _ = evaluate a b (SOSFinite.complexPolynomial SOSFinite.reflectedPolynomial) :=
      (SOSFinite.reflected_evaluation_eq_target a b).symm
    _ = _ := SOSFinite.reflected_sos_evaluation a b ha hb hab

end
end CGLMP5.SOS
