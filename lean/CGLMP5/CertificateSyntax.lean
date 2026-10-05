import CGLMP5.WordSyntax

/-! Typed exact-source syntax and a total canonical serializer. -/
namespace CGLMP5.CertificateSource

structure RawScalar where
  numerators : List Int
  denominator : Nat
  deriving DecidableEq, Repr

structure RawCoefficient where
  word : List (Nat × Nat)
  coefficient : RawScalar
  deriving DecidableEq, Repr

structure RawTerm where
  label : String
  weight : RawScalar
  polynomial : List RawCoefficient
  deriving DecidableEq, Repr

structure RawRational where
  numerator : Int
  denominator : Nat
  deriving DecidableEq, Repr

structure RawBox where
  lower : RawRational
  upper : RawRational
  deriving DecidableEq, Repr

def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')
def quote (s : String) : String := "\"" ++ s ++ "\""

def renderArray {α : Type} (render : Nat → α → String) (n : Nat) (xs : List α) : String :=
  if xs.isEmpty then "[]" else
    "[\n" ++ String.intercalate ",\n" (xs.map fun x => spaces (n + 2) ++ render (n + 2) x) ++
      "\n" ++ spaces n ++ "]"

def RawScalar.render (n : Nat) (s : RawScalar) : String :=
  "{\n" ++ spaces (n + 2) ++ "\"n\": " ++
    renderArray (fun _ v => quote (toString v)) (n + 2) s.numerators ++ ",\n" ++
    spaces (n + 2) ++ "\"d\": " ++ quote (toString s.denominator) ++ "\n" ++ spaces n ++ "}"

def renderFactor (n : Nat) (a : Nat × Nat) : String :=
  renderArray (fun _ v => toString v) n [a.1, a.2]

def RawCoefficient.render (n : Nat) (c : RawCoefficient) : String :=
  "{\n" ++ spaces (n + 2) ++ "\"word\": " ++
    renderArray renderFactor (n + 2) c.word ++ ",\n" ++
    spaces (n + 2) ++ "\"coefficient\": " ++ c.coefficient.render (n + 2) ++
    "\n" ++ spaces n ++ "}"

def RawTerm.render (n : Nat) (t : RawTerm) : String :=
  "{\n" ++ spaces (n + 2) ++ "\"id\": " ++ quote t.label ++ ",\n" ++
    spaces (n + 2) ++ "\"weight\": " ++ t.weight.render (n + 2) ++ ",\n" ++
    spaces (n + 2) ++ "\"polynomial\": " ++
    renderArray RawCoefficient.render (n + 2) t.polynomial ++ "\n" ++ spaces n ++ "}"

def RawRational.render (n : Nat) (q : RawRational) : String :=
  "{\n" ++ spaces (n + 2) ++ "\"numerator\": " ++ quote (toString q.numerator) ++ ",\n" ++
    spaces (n + 2) ++ "\"denominator\": " ++ quote (toString q.denominator) ++ "\n" ++ spaces n ++ "}"

def RawBox.render (n : Nat) (b : RawBox) : String :=
  "{\n" ++ spaces (n + 2) ++ "\"lower\": " ++ b.lower.render (n + 2) ++ ",\n" ++
    spaces (n + 2) ++ "\"upper\": " ++ b.upper.render (n + 2) ++ "\n" ++ spaces n ++ "}"

def renderBoxes (mu s u : RawBox) : String :=
  "{\n    \"mu\": " ++ mu.render 4 ++ ",\n    \"sqrt5\": " ++ s.render 4 ++
    ",\n    \"u\": " ++ u.render 4 ++ "\n  }"

/-- Typed integer data has no parser failure mode; denominator positivity is explicit. -/
def RawScalar.valid (s : RawScalar) : Prop :=
  s.numerators.length = 24 ∧ 0 < s.denominator

instance (s : RawScalar) : Decidable s.valid := by
  unfold RawScalar.valid
  exact inferInstance

def RawCoefficient.valid (c : RawCoefficient) : Prop :=
  c.coefficient.valid ∧ ∀ a ∈ c.word, a.1 < 4 ∧ 0 < a.2 ∧ a.2 < 5

instance (c : RawCoefficient) : Decidable c.valid := by
  unfold RawCoefficient.valid
  exact inferInstance

def RawTerm.valid (t : RawTerm) : Prop :=
  t.weight.valid ∧ ∀ c ∈ t.polynomial, c.valid

instance (t : RawTerm) : Decidable t.valid := by
  unfold RawTerm.valid
  exact inferInstance

/-- Even and odd source generators are split without changing within-party order. -/
def RawCoefficient.toWord (c : RawCoefficient) : Word :=
  ⟨(c.word.filter fun a => a.1 % 2 = 0).map fun a => (⟨a.1 / 2 % 2, Nat.mod_lt _ (by decide)⟩, a.2),
   (c.word.filter fun a => a.1 % 2 = 1).map fun a => (⟨a.1 / 2 % 2, Nat.mod_lt _ (by decide)⟩, a.2)⟩

end CGLMP5.CertificateSource
