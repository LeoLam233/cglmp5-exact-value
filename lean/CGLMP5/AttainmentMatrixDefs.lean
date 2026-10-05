import CGLMP5.AttainmentPhases
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace CGLMP5.Attainment
noncomputable section
open scoped BigOperators

/-- Algebraic measurement phases, literally the four Fourier offset choices. -/
def matrixPhaseExponent (r : Fin 4) (a j : Fin 5) : ℕ :=
  (![4*a.val, 21-4*a.val, 4*a.val+2, 19-4*a.val] r) * j.val

def localMatrix (r : Fin 4) (a : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => phase (matrixPhaseExponent r a i) * star (phase (matrixPhaseExponent r a j)) / 5

/-- Relabel D₂=A₁+1 and D₃=B₁+1 exactly as in the manuscript. -/
def localSpectral (r : Fin 4) : Matrix (Fin 5) (Fin 5) ℂ :=
  ∑ a : Fin 5, phase (4*(a.val + if 2 ≤ r.val then 1 else 0)) • localMatrix r a

def stepDest (r : Fin 4) (j : Fin 5) : Fin 5 :=
  ⟨if r.val%2 = 0 then (j.val+4)%5 else (j.val+1)%5, by split <;> omega⟩

def stepPhase (r : Fin 4) (j : Fin 5) : ℕ :=
  (![0, if j.val = 4 then 16 else 1, if j.val = 0 then 12 else 2,
       if j.val = 4 then 8 else 3] r)

/-- Concrete monomial local matrices, including wraparound phases. -/
def stepMatrix (r : Fin 4) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => if i = stepDest r j then phase (stepPhase r j) else 0

/-- General monomial multiplication, valid without any invertibility assumption. -/
lemma monomial_mul {n : Type*} [Fintype n] [DecidableEq n]
    (d e : n → n) (p q : n → ℂ) :
    Matrix.of (fun i j => if i = d j then p j else 0) *
      Matrix.of (fun i j => if i = e j then q j else 0) =
    Matrix.of (fun i j => if i = d (e j) then p (e j) * q j else 0) := by
  ext i j
  change (∑ k, (if i = d k then p k else 0) * (if k = e j then q j else 0)) = _
  simp [mul_ite]

end
end CGLMP5.Attainment
