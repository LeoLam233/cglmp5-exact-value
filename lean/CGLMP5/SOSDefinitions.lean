import CGLMP5.Words
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Fin

/-! Literal finite-Fourier Bell target used by the compact SOS identity. -/
namespace CGLMP5.SOS

noncomputable section

/-- The `k`th finite Fourier coefficient of `f(z)=1-z/2`. -/
def fourierCoeff (ω : ℂ) (k : ℕ) : ℂ :=
  ∑ z : Fin 5, ((2 - (z.val : ℂ)) / 10) * ω ^ ((5 - (k * z.val) % 5) % 5)

/-- The four cyclic edges after `D₂=A₁+1`, `D₃=B₁+1` relabelling. -/
def edgeWord (r : Fin 4) (k : ℕ) : Word :=
  match r.val with
  | 0 => ⟨[(0, k)], [(0, 5 - k)]⟩
  | 1 => ⟨[(1, 5 - k)], [(0, k)]⟩
  | 2 => ⟨[(1, k)], [(1, 5 - k)]⟩
  | _ => ⟨[(0, 5 - k)], [(1, k)]⟩

def edgeCoefficient (ω : ℂ) (r : Fin 4) (k : ℕ) : ℂ :=
  fourierCoeff ω k * (if r.val = 3 then ω ^ ((5 - k) % 5) else 1)

/-- The Bell polynomial is explicitly sixteen terms in every complex star-algebra. -/
def bell {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
    (ω : ℂ) (a b : Fin 2 → unitary R) : R :=
  ∑ r : Fin 4, ∑ k : Fin 4,
    edgeCoefficient ω r (k.val + 1) • Word.evalStar a b (edgeWord r (k.val + 1))

/-- Scalar coefficient syntax specialized to a finite ordered word list. -/
def evaluate {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
    (a b : Fin 2 → unitary R) (p : List (Word × ℂ)) : R :=
  (p.map fun t => t.2 • Word.evalStar a b t.1).sum

end
end CGLMP5.SOS
