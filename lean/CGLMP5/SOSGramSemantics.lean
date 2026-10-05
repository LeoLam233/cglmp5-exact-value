import CGLMP5.SOSPolynomial
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-! # Sound Gram-oriented expansion

The second term reverses the WORD factors only. Its coefficient remains
`d * star t.coefficient * u.coefficient`, as required by renaming the two summation indices.
-/

namespace CGLMP5.SOS
noncomputable section

/-- One row of the two-order Gram expansion. -/
def gramRow (d : ℂ) (t : Word × ℂ) (q : Polynomial) : Polynomial :=
  q.flatMap fun u =>
    [(Word.mul (Word.adjoint t.1) u.1, d * star t.2 * u.2),
     (Word.mul u.1 (Word.adjoint t.1), d * star t.2 * u.2)]

/-- Gram-oriented expansion with the same scalar coefficient on the two word orders. -/
def gramExpand (d : ℂ) (p : Polynomial) : Polynomial :=
  p.flatMap fun t => gramRow d t p

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (a b : Fin 2 → unitary R)
  (ha : ∀ i, a i ^ 5 = 1) (hb : ∀ i, b i ^ 5 = 1)
  (hab : ∀ i j, Commute (a i) (b j))

include ha hb hab in
theorem evaluate_gramRow (d : ℂ) (t : Word × ℂ) (q : Polynomial) :
    evaluate a b (gramRow d t q) =
      d • (star (t.2 • Word.evalStar a b t.1) * evaluate a b q +
        evaluate a b q * star (t.2 • Word.evalStar a b t.1)) := by
  induction q with
  | nil => simp [gramRow]
  | cons u q ih =>
    simp only [gramRow, List.flatMap_cons, evaluate_append] at ih ⊢
    simp only [evaluate_cons, evaluate_nil, add_zero, Word.evalStar_mul a b ha hb hab,
      Word.evalStar_adjoint a b ha hb hab, ih, star_smul, mul_add, add_mul,
      smul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [mul_assoc, mul_comm (u.2) (star t.2)]
    abel

include ha hb hab in
theorem evaluate_gramCross (d : ℂ) (p q : Polynomial) :
    evaluate a b (p.flatMap fun t => gramRow d t q) =
      d • (star (evaluate a b p) * evaluate a b q + evaluate a b q * star (evaluate a b p)) := by
  induction p with
  | nil => simp
  | cons t p ih =>
    rw [List.flatMap_cons, evaluate_append, evaluate_gramRow a b ha hb hab, ih, evaluate_cons]
    simp only [star_add, add_mul, mul_add, smul_add]
    abel

include ha hb hab in
/-- The optimized two-order Gram expansion has exactly the original anticommutator meaning. -/
theorem evaluate_gramExpand (d : ℂ) (p : Polynomial) :
    evaluate a b (gramExpand d p) =
      d • (star (evaluate a b p) * evaluate a b p + evaluate a b p * star (evaluate a b p)) :=
  evaluate_gramCross a b ha hb hab d p p


/-- Source entries factored into core and phase indices. -/
def phasePolynomial {Core Phase : Type*} (core : Core → ℂ) (phase : Phase → ℂ)
    (entries : List (Word × Core × Phase)) : Polynomial :=
  entries.map fun t => (t.1, core t.2.1 * phase t.2.2)

/-- The exact optimized pair expansion before substitution of its coefficient certificates. -/
def factoredGramExpand {Core Phase : Type*}
    (gram : Core → Core → ℂ) (phasePair : Phase → Phase → ℂ)
    (entries : List (Word × Core × Phase)) : Polynomial :=
  entries.flatMap fun t => entries.flatMap fun u =>
    [(Word.mul (Word.adjoint t.1) u.1, gram t.2.1 u.2.1 * phasePair t.2.2 u.2.2),
     (Word.mul u.1 (Word.adjoint t.1), gram t.2.1 u.2.1 * phasePair t.2.2 u.2.2)]

/-- Pointwise exact core and phase identities justify the complete optimized polynomial. -/
theorem factoredGramExpand_eq {Core Phase : Type*} (d : ℂ)
    (core : Core → ℂ) (phase : Phase → ℂ)
    (gram : Core → Core → ℂ) (phasePair : Phase → Phase → ℂ)
    (hgram : ∀ c e, gram c e = d * star (core c) * core e)
    (hphase : ∀ p q, phasePair p q = star (phase p) * phase q)
    (entries : List (Word × Core × Phase)) :
    factoredGramExpand gram phasePair entries = gramExpand d (phasePolynomial core phase entries) := by
  simp only [factoredGramExpand, gramExpand, gramRow, phasePolynomial, List.flatMap_map]
  apply List.flatMap_congr
  intro t _
  apply List.flatMap_congr
  intro u _
  have h : gram t.2.1 u.2.1 * phasePair t.2.2 u.2.2 =
      d * star (core t.2.1 * phase t.2.2) * (core u.2.1 * phase u.2.2) := by
    rw [hgram, hphase, star_mul]
    ring
  simp only [Function.comp_apply, h]

include ha hb hab in
/-- The phase/core optimized expansion evaluates to the original anticommutator. -/
theorem evaluate_factoredGramExpand {Core Phase : Type*} (d : ℂ)
    (core : Core → ℂ) (phase : Phase → ℂ)
    (gram : Core → Core → ℂ) (phasePair : Phase → Phase → ℂ)
    (hgram : ∀ c e, gram c e = d * star (core c) * core e)
    (hphase : ∀ p q, phasePair p q = star (phase p) * phase q)
    (entries : List (Word × Core × Phase)) :
    evaluate a b (factoredGramExpand gram phasePair entries) =
      d • (star (evaluate a b (phasePolynomial core phase entries)) *
        evaluate a b (phasePolynomial core phase entries) +
        evaluate a b (phasePolynomial core phase entries) *
        star (evaluate a b (phasePolynomial core phase entries))) := by
  rw [factoredGramExpand_eq d core phase gram phasePair hgram hphase]
  exact evaluate_gramExpand a b ha hb hab d _

end
end CGLMP5.SOS
