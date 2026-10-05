import CGLMP5.CertificateSyntax
import CGLMP5.Words
import Mathlib.Tactic.IntervalCases

/-!
# Literal source-word interpretation

The source labels are exactly `0=A₀`, `1=B₀`, `2=A₁`, `3=B₁`.
Filtering into two party lists preserves evaluation because only cross-party
factors are moved. No same-party commutation or order-five relation is needed.
-/

namespace CGLMP5.CertificateSource

/-- The four source labels are interpreted literally. Invalid labels map to one,
but the bridge theorem requires every label to be less than four. -/
def sourceGenerator {M : Type*} [Monoid M] (a b : Fin 2 → M) : ℕ → M
  | 0 => a 0
  | 1 => b 0
  | 2 => a 1
  | 3 => b 1
  | _ => 1

/-- Ordered product of the source factors, before party separation. -/
def sourceEval {M : Type*} [Monoid M] (a b : Fin 2 → M) (w : List (ℕ × ℕ)) : M :=
  (w.map fun t => sourceGenerator a b t.1 ^ t.2).prod

def separateSourceWord (w : List (ℕ × ℕ)) : Word :=
  ⟨(w.filter fun t => t.1 % 2 = 0).map fun t =>
      (⟨t.1 / 2 % 2, Nat.mod_lt _ (by decide)⟩, t.2),
   (w.filter fun t => t.1 % 2 = 1).map fun t =>
      (⟨t.1 / 2 % 2, Nat.mod_lt _ (by decide)⟩, t.2)⟩

lemma RawCoefficient.toWord_eq_separate (c : RawCoefficient) :
    c.toWord = separateSourceWord c.word := rfl

lemma alice_word_commutes_bob_power {M : Type*} [Monoid M] (a b : Fin 2 → M)
    (hab : ∀ i j, Commute (a i) (b j)) (w : PartyWord) (j : Fin 2) (n : ℕ) :
    Commute (PartyWord.eval a w) (b j ^ n) := by
  simpa only [PartyWord.eval_cons, PartyWord.eval_nil, mul_one] using
    PartyWord.eval_commute a b hab w [(j,n)]

/-- Party separation retains the original ordered source product. -/
lemma eval_separateSourceWord {M : Type*} [Monoid M] (a b : Fin 2 → M)
    (hab : ∀ i j, Commute (a i) (b j)) (w : List (ℕ × ℕ))
    (hvalid : ∀ t ∈ w, t.1 < 4) :
    Word.eval a b (separateSourceWord w) = sourceEval a b w := by
  induction w with
  | nil => simp [separateSourceWord, sourceEval, Word.eval]
  | cons t w ih =>
    have ht : t.1 < 4 := hvalid t (by simp)
    have hw : ∀ r ∈ w, r.1 < 4 := fun r hr => hvalid r (by simp [hr])
    specialize ih hw
    rcases t with ⟨r,n⟩
    dsimp at ht
    have h0 := alice_word_commutes_bob_power a b hab (separateSourceWord w).alice 0 n
    have h1 := alice_word_commutes_bob_power a b hab (separateSourceWord w).alice 1 n
    interval_cases r
    · simp only [separateSourceWord, List.filter_cons, Nat.zero_mod, beq_self_eq_true,
        List.map_cons, Word.eval, PartyWord.eval_cons] at *
      simpa [sourceEval, sourceGenerator, separateSourceWord, Word.eval, mul_assoc] using
        congrArg (fun z => a 0 ^ n * z) ih
    · change Word.eval a b (separateSourceWord ((1,n)::w)) = b 0 ^ n * sourceEval a b w
      rw [← ih]
      simpa [separateSourceWord, Word.eval, ← mul_assoc] using
        congrArg (fun z => z * PartyWord.eval b (separateSourceWord w).bob) h0.eq
    · simpa [sourceEval, sourceGenerator, separateSourceWord, Word.eval, mul_assoc] using
        congrArg (fun z => a 1 ^ n * z) ih
    · change Word.eval a b (separateSourceWord ((3,n)::w)) = b 1 ^ n * sourceEval a b w
      rw [← ih]
      simpa [separateSourceWord, Word.eval, ← mul_assoc] using
        congrArg (fun z => z * PartyWord.eval b (separateSourceWord w).bob) h1.eq

lemma RawCoefficient.eval_toWord {M : Type*} [Monoid M] (a b : Fin 2 → M)
    (hab : ∀ i j, Commute (a i) (b j)) (c : RawCoefficient)
    (hvalid : ∀ t ∈ c.word, t.1 < 4) :
    Word.eval a b c.toWord = sourceEval a b c.word :=
  eval_separateSourceWord a b hab c.word hvalid

lemma RawCoefficient.evalStar_toWord {R : Type*} [Monoid R] [StarMul R]
    (a b : Fin 2 → unitary R) (hab : ∀ i j, Commute (a i) (b j))
    (c : RawCoefficient) (hvalid : c.valid) :
    Word.evalStar a b c.toWord = (sourceEval a b c.word : unitary R) := by
  exact congrArg Subtype.val
    (c.eval_toWord a b hab fun t ht => (hvalid.2 t ht).1)

/-- Literal ordered product in the represented star-monoid. -/
def rawEval {R : Type*} [Monoid R] [StarMul R]
    (a b : Fin 2 → unitary R) (w : List (ℕ × ℕ)) : R :=
  (w.map fun t => ((sourceGenerator a b t.1 : unitary R) : R)^t.2).prod

lemma rawEval_eq_sourceEval {R : Type*} [Monoid R] [StarMul R]
    (a b : Fin 2 → unitary R) (w : List (ℕ × ℕ)) :
    rawEval a b w = ((sourceEval a b w : unitary R) : R) := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    simp only [rawEval, sourceEval, List.map_cons, List.prod_cons,
      Submonoid.coe_mul, SubmonoidClass.coe_pow] at *
    rw [ih]

/-- The decoded source coefficient has its literal original evaluation. -/
lemma rawCoefficient_eval {R : Type*} [Monoid R] [StarMul R]
    (a b : Fin 2 → unitary R) (hab : ∀ i j, Commute (a i) (b j))
    (c : RawCoefficient) (hvalid : c.valid) :
    rawEval a b c.word = Word.evalStar a b c.toWord := by
  rw [rawEval_eq_sourceEval]
  exact (c.evalStar_toWord a b hab hvalid).symm

end CGLMP5.CertificateSource
