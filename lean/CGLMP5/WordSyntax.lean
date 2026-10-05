import Init

/-! Pure ordered word syntax. No algebra, analysis or scalar interpretation is imported. -/
namespace CGLMP5

abbrev Letter := Fin 2 × Nat
abbrev PartyWord := List Letter

namespace PartyWord

/-- Insert a factor, reducing its exponent and combining only an equal head. -/
def push (a : Letter) (w : PartyWord) : PartyWord :=
  let k := a.2 % 5
  if k = 0 then w else
    match w with
    | [] => [(a.1, k)]
    | b :: t =>
      if a.1 = b.1 then
        let m := (k + b.2) % 5
        if m = 0 then t else (a.1, m) :: t
      else (a.1, k) :: w

/-- A right-to-left, order-preserving adjacent-power reduction. -/
def reduce : PartyWord → PartyWord
  | [] => []
  | a :: w => push a (reduce w)

/-- Formal adjoint reverses order and uses the inverse exponent modulo five. -/
def adjoint (w : PartyWord) : PartyWord :=
  reduce (w.reverse.map fun a => (a.1, 5 - a.2 % 5))

end PartyWord

/-- Two ordered party lists. Same-party generator order is part of the data. -/
structure Word where
  alice : PartyWord
  bob : PartyWord
  deriving DecidableEq, Repr

namespace Word

def one : Word := ⟨[], []⟩
def mul (v w : Word) : Word :=
  ⟨PartyWord.reduce (v.alice ++ w.alice), PartyWord.reduce (v.bob ++ w.bob)⟩
def adjoint (w : Word) : Word :=
  ⟨PartyWord.adjoint w.alice, PartyWord.adjoint w.bob⟩

end Word
end CGLMP5
