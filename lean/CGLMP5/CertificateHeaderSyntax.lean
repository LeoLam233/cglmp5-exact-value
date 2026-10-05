import CGLMP5.SourceDecimalSoundness

/-! Lossless decimal syntax for the canonical embedding boxes and Schmidt coefficients. -/
namespace CGLMP5.CertificateSource

structure TextRational where
  numerator : String
  denominator : String

structure TextBox where
  lower : TextRational
  upper : TextRational

structure ChunkRational where
  numerator : DecimalChunks
  denominator : DecimalChunks

structure ChunkBox where
  lower : ChunkRational
  upper : ChunkRational

def TextRational.decode (q : TextRational) : Option RawRational := do
  let n ← decimalInt q.numerator
  let d ← decimalNat q.denominator
  pure ⟨n,d⟩

def TextBox.decode (b : TextBox) : Option RawBox := do
  let l ← b.lower.decode
  let u ← b.upper.decode
  pure ⟨l,u⟩

def ChunkRational.decode (q : ChunkRational) : Option RawRational := do
  let n ← q.numerator.integer
  if q.denominator.negative then none else do
    let d ← q.denominator.natural
    pure ⟨n,d⟩

def ChunkBox.decode (b : ChunkBox) : Option RawBox := do
  let l ← b.lower.decode
  let u ← b.upper.decode
  pure ⟨l,u⟩

def ChunkRational.toText (q : ChunkRational) : TextRational :=
  ⟨q.numerator.text, q.denominator.text⟩

def ChunkBox.toText (b : ChunkBox) : TextBox :=
  ⟨b.lower.toText, b.upper.toText⟩

def TextRational.renderLines (n : Nat) (q : TextRational) : List String :=
  ["{", spaces (n+2) ++ "\"numerator\": " ++ quote q.numerator ++ ",",
    spaces (n+2) ++ "\"denominator\": " ++ quote q.denominator, spaces n ++ "}"]

def TextBox.renderLines (n : Nat) (b : TextBox) : List String :=
  ["{"] ++ prefixLine (spaces (n+2) ++ "\"lower\": ") (suffixLine "," (b.lower.renderLines (n+2))) ++
    prefixLine (spaces (n+2) ++ "\"upper\": ") (b.upper.renderLines (n+2)) ++ [spaces n ++ "}"]

def textBoxesLines (mu s u : TextBox) : List String :=
  ["{"] ++ prefixLine "    \"mu\": " (suffixLine "," (mu.renderLines 4)) ++
    prefixLine "    \"sqrt5\": " (suffixLine "," (s.renderLines 4)) ++
    prefixLine "    \"u\": " (u.renderLines 4) ++ ["  }"]

/-- Chunk boundaries do not alter the parsed rational. -/
theorem ChunkRational.decode_sound {q : ChunkRational} {r : RawRational}
    (h : q.decode = some r) : q.toText.decode = some r := by
  cases hn : q.numerator.integer with
  | none => simp [ChunkRational.decode, hn] at h
  | some n =>
    have hnum := DecimalChunks.integer_sound hn
    cases hb : q.denominator.negative with
    | true => simp [ChunkRational.decode, hn, hb] at h
    | false =>
      cases hd : q.denominator.natural with
      | none => simp [ChunkRational.decode, hn, hb, hd] at h
      | some d =>
        have hden : decimalNat q.denominator.text = some d := by
          simpa [DecimalChunks.text, hb] using DecimalChunks.natural_sound hd
        have he : (⟨n,d⟩ : RawRational) = r := by
          simpa [ChunkRational.decode, hn, hb, hd] using h
        subst r
        simp [ChunkRational.toText, TextRational.decode, hnum, hden]

/-- Both endpoints have the semantics of their uninterrupted original decimal strings. -/
theorem ChunkBox.decode_sound {b : ChunkBox} {r : RawBox}
    (h : b.decode = some r) : b.toText.decode = some r := by
  cases hl : b.lower.decode with
  | none => simp [ChunkBox.decode, hl] at h
  | some l =>
    cases hu : b.upper.decode with
    | none => simp [ChunkBox.decode, hl, hu] at h
    | some u =>
      have he : (⟨l,u⟩ : RawBox) = r := by simpa [ChunkBox.decode, hl, hu] using h
      subst r
      simp [ChunkBox.toText, TextBox.decode, ChunkRational.decode_sound hl,
        ChunkRational.decode_sound hu]

end CGLMP5.CertificateSource
