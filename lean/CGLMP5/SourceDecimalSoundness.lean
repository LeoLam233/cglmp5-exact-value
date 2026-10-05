import CGLMP5.CertificateChunks
import Mathlib.Tactic.Ring

/-! Positional soundness of source decimal chunks. The proofs are generic;
no large source string is constructed or parsed during these proofs. -/

namespace CGLMP5.CertificateSource

/-- The same checked decimal fold as `decimalNatChars`, with a supplied prefix. -/
def decimalFold (cs : List Char) (acc : Nat) : Option Nat :=
  cs.foldlM (fun n c =>
    if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (10*n+(c.toNat-48)) else none) acc

@[simp] lemma decimalFold_nil (acc : Nat) : decimalFold [] acc = some acc := rfl

lemma decimalFold_cons (c : Char) (cs : List Char) (acc : Nat) :
    decimalFold (c::cs) acc =
      if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then decimalFold cs (10*acc+(c.toNat-48)) else none := by
  simp only [decimalFold, List.foldlM_cons]
  split <;> simp_all

/-- Appending `k` decimal digits multiplies the existing prefix by `10^k`. -/
lemma decimalFold_affine (cs : List Char) (acc : Nat) :
    decimalFold cs acc = (decimalFold cs 0).map (fun v => acc*10^cs.length+v) := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [decimalFold_cons, decimalFold_cons]
    by_cases hc : 48 ≤ c.toNat ∧ c.toNat ≤ 57
    · simp only [hc, and_self, ite_true, mul_zero, zero_add]
      rw [ih (10*acc+(c.toNat-48)), ih (c.toNat-48)]
      simp only [Option.map_map, List.length_cons]
      congr 1
      funext v
      simp only [Function.comp_apply, pow_succ]
      ring
    · simp [hc]

lemma decimalFold_append (cs ds : List Char) (acc : Nat) :
    decimalFold (cs++ds) acc = (decimalFold cs acc).bind (decimalFold ds) := by
  rw [decimalFold, List.foldlM_append]
  rfl

lemma chunkNat_nonempty {c : String} {v : Nat} (h : chunkNat c = some v) : c.toList ≠ [] := by
  intro he
  simp [chunkNat, decimalNat, decimalNatChars, he] at h

lemma chunkNat_fold {c : String} {v : Nat} (h : chunkNat c = some v) (acc : Nat) :
    decimalFold c.toList acc = some (acc*10^c.length+v) := by
  have hne := chunkNat_nonempty h
  have hp : decimalFold c.toList 0 = some v := by
    unfold chunkNat at h
    split at h
    · simpa only [decimalNat, decimalNatChars, List.isEmpty_eq_false_iff.mpr hne,
        Bool.false_eq_true, ite_false, decimalFold] using h
    · contradiction
  rw [decimalFold_affine, hp]
  simp only [Option.map_some, String.length_toList]

/-- Checked chunk accumulation has exactly the value of the concatenated digits. -/
lemma chunkFold_sound (cs : List String) (acc n : Nat)
    (h : cs.foldlM (fun a c => (chunkNat c).map (fun v => a*10^c.length+v)) acc = some n) :
    decimalFold (cs.flatMap String.toList) acc = some n := by
  induction cs generalizing acc with
  | nil => simpa using h
  | cons c cs ih =>
    simp only [List.foldlM_cons] at h
    cases hc : chunkNat c with
    | none => simp [hc] at h
    | some v =>
      simp only [hc, Option.map_some, Option.bind_some] at h
      rw [List.flatMap_cons, decimalFold_append, chunkNat_fold hc acc]
      exact ih (acc*10^c.length+v) h


/-- A successful nonempty chunk list decodes to exactly the uninterrupted decimal string. -/
theorem DecimalChunks.natural_sound {d : DecimalChunks} {n : Nat}
    (h : d.natural = some n) : decimalNat (String.join d.chunks) = some n := by
  rcases d with ⟨negative, cs⟩
  cases cs with
  | nil => simp [DecimalChunks.natural] at h
  | cons c cs =>
    simp only [DecimalChunks.natural, List.isEmpty_cons, Bool.false_eq_true, ite_false] at h
    have hp := chunkFold_sound (c::cs) 0 n h
    have hfirst : c.toList ≠ [] := by
      cases hc : chunkNat c with
      | none => simp [List.foldlM_cons, hc] at h
      | some v => exact chunkNat_nonempty hc
    have hne : ((c::cs).flatMap String.toList) ≠ [] := by
      rw [List.flatMap_cons]
      intro he
      exact hfirst (List.append_eq_nil_iff.mp he).1
    simpa only [decimalNat, decimalNatChars, String.toList_join,
      List.isEmpty_eq_false_iff.mpr hne, Bool.false_eq_true, ite_false, decimalFold] using hp

/-- An unsigned successful decimal parse cannot hide an integer sign prefix. -/
lemma decimalInt_of_decimalNat {s : String} {n : Nat} (h : decimalNat s = some n) :
    decimalInt s = some (n : Int) := by
  cases hc : s.toList with
  | nil => simp [decimalNat, decimalNatChars, hc] at h
  | cons c cs =>
    by_cases hm : c = '-'
    · subst c
      simp [decimalNat, decimalNatChars, hc, List.foldlM_cons] at h
    · have hf : decimalNatChars (c::cs) = some n := by simpa [decimalNat, hc] using h
      simp [decimalInt, hc, hm, hf]

/-- Integer source fragments retain both positional value and the exact sign convention. -/
theorem DecimalChunks.integer_sound {d : DecimalChunks} {z : Int}
    (h : d.integer = some z) : decimalInt d.text = some z := by
  unfold DecimalChunks.integer at h
  cases hn : d.natural with
  | none => simp [hn] at h
  | some n =>
    have hp := DecimalChunks.natural_sound hn
    cases hb : d.negative with
    | false =>
      have hz : (n : Int) = z := by simpa [hn, hb] using h
      subst z
      simpa [DecimalChunks.text, hb] using decimalInt_of_decimalNat hp
    | true =>
      have hz : -(n : Int) = z := by simpa [hn, hb] using h
      subst z
      simp only [DecimalChunks.text, hb, ite_true, decimalInt, String.toList_append]
      simp only [decimalNat, String.toList_join] at hp
      simp only [show "-".toList = ['-'] from rfl, List.cons_append, List.nil_append,
        String.toList_join]
      rw [hp]
      rfl


/-- Successful list decoding transports along a pointwise sound decoder refinement. -/
lemma option_mapM_sound {α β : Type*} (f g : α → Option β)
    (sound : ∀ a b, f a = some b → g a = some b)
    (xs : List α) (ys : List β) (h : xs.mapM f = some ys) : xs.mapM g = some ys := by
  induction xs generalizing ys with
  | nil => simpa using h
  | cons a xs ih =>
    cases hf : f a with
    | none => simp [List.mapM_cons, hf] at h
    | some b =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons, hf, ht] at h
      | some bs =>
        have he : b::bs = ys := by simpa [List.mapM_cons, hf, ht] using h
        subst ys
        simp [List.mapM_cons, sound a b hf, ih bs ht]

/-- Every successful chunk scalar is the same scalar parsed from the exact original decimal text. -/
theorem ChunkScalar.decode_sound {s : ChunkScalar} {r : RawScalar}
    (h : s.decode = some r) : s.toText.decode = some r := by
  cases hn : s.numerators.mapM DecimalChunks.integer with
  | none => simp [ChunkScalar.decode, hn] at h
  | some ns =>
    have hns : (s.numerators.map DecimalChunks.text).mapM decimalInt = some ns := by
      simpa only [List.mapM_map, Function.comp_def] using
        option_mapM_sound DecimalChunks.integer (fun d => decimalInt d.text)
          (fun d z hd => DecimalChunks.integer_sound hd) s.numerators ns hn
    cases hb : s.denominator.negative with
    | true => simp [ChunkScalar.decode, hn, hb] at h
    | false =>
      cases hd : s.denominator.natural with
      | none => simp [ChunkScalar.decode, hn, hb, hd] at h
      | some d =>
        have hden : decimalNat s.denominator.text = some d := by
          simpa [DecimalChunks.text, hb] using DecimalChunks.natural_sound hd
        have he : (⟨ns,d⟩ : RawScalar) = r := by
          simpa [ChunkScalar.decode, hn, hb, hd] using h
        subst r
        simp [ChunkScalar.toText, TextScalar.decode, hns, hden]

/-- Coefficient words are untouched while decimal scalar parsing is semantically preserved. -/
theorem ChunkCoefficient.decode_sound {c : ChunkCoefficient} {r : RawCoefficient}
    (h : c.decode = some r) : c.toText.decode = some r := by
  cases hc : c.coefficient.decode with
  | none => simp [ChunkCoefficient.decode, hc] at h
  | some s =>
    have hs := ChunkScalar.decode_sound hc
    have he : (⟨c.word,s⟩ : RawCoefficient) = r := by
      simpa [ChunkCoefficient.decode, hc] using h
    subst r
    simp [ChunkCoefficient.toText, TextCoefficient.decode, hs]

/-- Full compact terms decoded from chunks equal decoding of their uninterrupted source text. -/
theorem ChunkTerm.decode_sound {t : ChunkTerm} {r : RawTerm}
    (h : t.decode = some r) : t.toText.decode = some r := by
  cases hw : t.weight.decode with
  | none => simp [ChunkTerm.decode, hw] at h
  | some w =>
    cases hp : t.polynomial.mapM ChunkCoefficient.decode with
    | none => simp [ChunkTerm.decode, hw, hp] at h
    | some ps =>
      have hw' := ChunkScalar.decode_sound hw
      have hp' : (t.polynomial.map ChunkCoefficient.toText).mapM TextCoefficient.decode = some ps := by
        simpa only [List.mapM_map, Function.comp_def] using
          option_mapM_sound ChunkCoefficient.decode (fun c => c.toText.decode)
            (fun c r hc => ChunkCoefficient.decode_sound hc) t.polynomial ps hp
      have he : (⟨t.label,w,ps⟩ : RawTerm) = r := by
        simpa [ChunkTerm.decode, hw, hp] using h
      subst r
      simp [ChunkTerm.toText, TextTerm.decode, hw', hp']

end CGLMP5.CertificateSource
