import CGLMP5.CertificateRender

namespace CGLMP5.CertificateSource

/-- Total ASCII decimal parser, rejecting empty strings and nondigits. -/
def decimalNatChars (cs : List Char) : Option Nat :=
  if cs.isEmpty then none else
    cs.foldlM (fun n c =>
      if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (10*n+(c.toNat-48)) else none) 0

def decimalInt (s : String) : Option Int :=
  match s.toList with
  | '-' :: cs => (decimalNatChars cs).map (fun n => -(n : Int))
  | cs => (decimalNatChars cs).map (fun n => (n : Int))

def decimalNat (s : String) : Option Nat := decimalNatChars s.toList

structure TextScalar where
  numerators : List String
  denominator : String
  deriving Repr

def TextScalar.decode (s : TextScalar) : Option RawScalar := do
  let ns ← s.numerators.mapM decimalInt
  let d ← decimalNat s.denominator
  pure ⟨ns,d⟩

def TextScalar.renderLines (n : Nat) (s : TextScalar) : List String :=
  ["{"] ++ prefixLine (spaces (n+2) ++ "\"n\": ")
    (suffixLine "," (arrayLines (fun _ v => [quote v]) (n+2) s.numerators)) ++
    [spaces (n+2) ++ "\"d\": " ++ quote s.denominator, spaces n ++ "}"]

structure TextCoefficient where
  word : List (Nat × Nat)
  coefficient : TextScalar

def TextCoefficient.decode (c : TextCoefficient) : Option RawCoefficient :=
  c.coefficient.decode.map (fun s => ⟨c.word,s⟩)

def TextCoefficient.renderLines (n : Nat) (c : TextCoefficient) : List String :=
  ["{"] ++ prefixLine (spaces (n+2) ++ "\"word\": ")
    (suffixLine "," (arrayLines factorLines (n+2) c.word)) ++
    prefixLine (spaces (n+2) ++ "\"coefficient\": ") (c.coefficient.renderLines (n+2)) ++
    [spaces n ++ "}"]

structure TextTerm where
  label : String
  weight : TextScalar
  polynomial : List TextCoefficient

def TextTerm.decode (t : TextTerm) : Option RawTerm := do
  let w ← t.weight.decode
  let p ← t.polynomial.mapM TextCoefficient.decode
  pure ⟨t.label,w,p⟩

def TextTerm.renderLines (n : Nat) (t : TextTerm) : List String :=
  ["{", spaces (n+2) ++ "\"id\": " ++ quote t.label ++ ","] ++
    prefixLine (spaces (n+2) ++ "\"weight\": ") (suffixLine "," (t.weight.renderLines (n+2))) ++
    prefixLine (spaces (n+2) ++ "\"polynomial\": ")
      (arrayLines TextCoefficient.renderLines (n+2) t.polynomial) ++ [spaces n ++ "}"]

end CGLMP5.CertificateSource
