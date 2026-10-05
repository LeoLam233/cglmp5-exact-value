import CGLMP5.CertificateText

namespace CGLMP5.CertificateSource

/-- Long decimal strings are represented by ordered at-most-nine-byte source fragments.
This is a lossless source representation, not a numerical approximation. -/
structure DecimalChunks where
  negative : Bool
  chunks : List String
  deriving Repr

/-- Total fragment parser; each fragment contains one to nine decimal digits. -/
def chunkNat (s : String) : Option Nat :=
  if s.length ≤ 9 then decimalNat s else none

def DecimalChunks.natural (d : DecimalChunks) : Option Nat :=
  if d.chunks.isEmpty then none else
    d.chunks.foldlM (fun n c => (chunkNat c).map (fun v => n*10^c.length+v)) 0

def DecimalChunks.integer (d : DecimalChunks) : Option Int :=
  d.natural.map (fun n => if d.negative then -(n:Int) else (n:Int))

/-- Exact original decimal bytes, reconstructed without any arithmetic conversion. -/
def DecimalChunks.text (d : DecimalChunks) : String :=
  (if d.negative then "-" else "") ++ String.join d.chunks

structure ChunkScalar where
  numerators : List DecimalChunks
  denominator : DecimalChunks

def ChunkScalar.decode (s : ChunkScalar) : Option RawScalar := do
  let ns ← s.numerators.mapM DecimalChunks.integer
  if s.denominator.negative then none else do
    let d ← s.denominator.natural
    pure ⟨ns,d⟩

def ChunkScalar.toText (s : ChunkScalar) : TextScalar :=
  ⟨s.numerators.map DecimalChunks.text, s.denominator.text⟩

structure ChunkCoefficient where
  word : List (Nat × Nat)
  coefficient : ChunkScalar

def ChunkCoefficient.decode (c : ChunkCoefficient) : Option RawCoefficient :=
  c.coefficient.decode.map (fun s => ⟨c.word,s⟩)

def ChunkCoefficient.toText (c : ChunkCoefficient) : TextCoefficient :=
  ⟨c.word,c.coefficient.toText⟩

structure ChunkTerm where
  label : String
  weight : ChunkScalar
  polynomial : List ChunkCoefficient

def ChunkTerm.decode (t : ChunkTerm) : Option RawTerm := do
  let w ← t.weight.decode
  let p ← t.polynomial.mapM ChunkCoefficient.decode
  pure ⟨t.label,w,p⟩

def ChunkTerm.toText (t : ChunkTerm) : TextTerm :=
  ⟨t.label,t.weight.toText,t.polynomial.map ChunkCoefficient.toText⟩

end CGLMP5.CertificateSource
