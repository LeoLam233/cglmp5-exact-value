import Mathlib.Data.Rat.Init
import Mathlib.Data.Fin.Basic

/-! Pure exact scalar syntax; no actual root, real analysis or trigonometry. -/

namespace CGLMP5

/-- Ordered rational coordinates `a+2*b+6*c+12*e` of the canonical tower. -/
abbrev Scalar := Fin 24 → ℚ

namespace Scalar

/-- Canonical integer numerator and positive-denominator decoding.
Positivity of each supplied denominator is checked separately in the data module. -/
def ofCanonical (n : Fin 24 → ℤ) (d : ℕ) : Scalar := fun k => (n k : ℚ) / d

def zero : Scalar := fun _ => 0
def add (a b : Scalar) : Scalar := fun k => a k + b k
def neg (a : Scalar) : Scalar := fun k => -a k
def ofRat (q : ℚ) : Scalar := fun k => if k = 0 then q else 0
def conj (a : Scalar) : Scalar := fun k => if k.val < 12 then a k else -a k

def isReal (a : Scalar) : Prop := ∀ k : Fin 24, 12 ≤ k.val → a k = 0

instance (a : Scalar) : Decidable (isReal a) := by
  unfold isReal
  infer_instance

end Scalar
end CGLMP5
