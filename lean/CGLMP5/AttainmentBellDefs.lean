import CGLMP5.AttainmentMatrixDefs
import CGLMP5.SOSDefinitions

namespace CGLMP5.Attainment
noncomputable section
open scoped BigOperators Matrix Kronecker

def stepIter (r : Fin 4) : ℕ → Fin 5 → Fin 5
  | 0, j => j
  | n+1, j => stepDest r (stepIter r n j)

def phaseIter (r : Fin 4) : ℕ → Fin 5 → ℕ
  | 0, _ => 0
  | n+1, j => stepPhase r (stepIter r n j) + phaseIter r n j

/-- All matrix powers are computed by genuine matrix multiplication. -/
lemma stepMatrix_pow (r : Fin 4) (n : ℕ) :
    stepMatrix r ^ n = Matrix.of (fun i j =>
      if i = stepIter r n j then phase (phaseIter r n j) else 0) := by
  induction n with
  | zero => ext i j; simp [stepIter, phaseIter, phase_zero, Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ', ih]
    change Matrix.of (fun i j => if i = stepDest r j then phase (stepPhase r j) else 0) *
      Matrix.of (fun i j => if i = stepIter r n j then phase (phaseIter r n j) else 0) = _
    rw [monomial_mul]
    ext i j
    simp [stepIter, phaseIter, phase_add]

/-- Sixteen terms of the full physical Bell operator, with the exact word order. -/
def edgeMatrix (r : Fin 4) (k : ℕ) : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ :=
  match r.val with
  | 0 => (stepMatrix 0 ^ k) ⊗ₖ (stepMatrix 1 ^ (5-k))
  | 1 => (stepMatrix 2 ^ (5-k)) ⊗ₖ (stepMatrix 1 ^ k)
  | 2 => (stepMatrix 2 ^ k) ⊗ₖ (stepMatrix 3 ^ (5-k))
  | _ => (stepMatrix 0 ^ (5-k)) ⊗ₖ (stepMatrix 3 ^ k)

def matrixBell : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ :=
  ∑ r : Fin 4, ∑ k : Fin 4, SOS.edgeCoefficient (zeta^4) r (k.val+1) •
    edgeMatrix r (k.val+1)

def distanceIndex (i j : Fin 5) : Fin 5 :=
  ⟨if i.val ≤ j.val then j.val-i.val else i.val-j.val, by split <;> omega⟩

def toeplitzEntry (i j : Fin 5) : ℂ :=
  (![0, (u : ℂ)*(5-(s : ℂ))/20, ((s : ℂ)-1)/2,
      (u : ℂ)*(s : ℂ)/10, ((s : ℂ)+1)/2] (distanceIndex i j))


lemma stepIter_opposite : ∀ (k : Fin 4) (l : Fin 5),
    stepIter 0 (k.val+1) l = stepIter 1 (5-(k.val+1)) l ∧
    stepIter 2 (5-(k.val+1)) l = stepIter 1 (k.val+1) l ∧
    stepIter 2 (k.val+1) l = stepIter 3 (5-(k.val+1)) l ∧
    stepIter 0 (5-(k.val+1)) l = stepIter 3 (k.val+1) l := by decide

lemma same_destination_zero (d : Fin 5) (i j : Fin 5) (p q : ℂ) (h : i ≠ j) :
    (if i = d then p else 0) * (if j = d then q else 0) = 0 := by
  by_cases hi : i = d
  · subst i; simp [Ne.symm h]
  · simp [hi]

/-- Every individual Bell word preserves the full diagonal Schmidt subspace. -/
lemma edgeMatrix_off_diagonal (r : Fin 4) (k : Fin 4) (i j l : Fin 5) (h : i ≠ j) :
    edgeMatrix r (k.val+1) (i,j) (l,l) = 0 := by
  have hd := stepIter_opposite k l
  fin_cases r
  · simp only [edgeMatrix, stepMatrix_pow, Matrix.kroneckerMap_apply, Matrix.of_apply]
    rw [← hd.1]
    exact same_destination_zero _ i j _ _ h
  · simp only [edgeMatrix, stepMatrix_pow, Matrix.kroneckerMap_apply, Matrix.of_apply]
    rw [← hd.2.1]
    exact same_destination_zero _ i j _ _ h
  · simp only [edgeMatrix, stepMatrix_pow, Matrix.kroneckerMap_apply, Matrix.of_apply]
    rw [← hd.2.2.1]
    exact same_destination_zero _ i j _ _ h
  · simp only [edgeMatrix, stepMatrix_pow, Matrix.kroneckerMap_apply, Matrix.of_apply]
    rw [← hd.2.2.2]
    exact same_destination_zero _ i j _ _ h

/-- The20 off-diagonal output coordinates vanish for each of five diagonal inputs. -/
lemma matrixBell_off_diagonal (i j l : Fin 5) (h : i ≠ j) : matrixBell (i,j) (l,l) = 0 := by
  simp [matrixBell, Matrix.sum_apply, Matrix.smul_apply, edgeMatrix_off_diagonal _ _ i j l h]

end
end CGLMP5.Attainment
