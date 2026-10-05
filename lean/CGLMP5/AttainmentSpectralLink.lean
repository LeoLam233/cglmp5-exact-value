import CGLMP5.AttainmentSpectral0
import CGLMP5.AttainmentSpectral1
import CGLMP5.AttainmentSpectral2
import CGLMP5.AttainmentSpectral3
import CGLMP5.AttainmentFourierFormula
import CGLMP5.AttainmentOperatorLink
import CGLMP5.AttainmentCoefficient
import CGLMP5.BellBridge

namespace CGLMP5.Attainment
noncomputable section
open scoped BigOperators Matrix Kronecker

abbrev H5 := EuclideanSpace ℂ (Fin 5)
abbrev H25 := EuclideanSpace ℂ (Fin 5 × Fin 5)

def alicePVM (x : Fin 2) : PVM (Op H5) := localPVM (aliceIndex x)
def bobPVM (y : Fin 2) : PVM (Op H5) := localPVM (bobIndex y)

lemma omega_unit : star (zeta^4) * zeta^4 = 1 := by
  rw [← phase_eq_pow]
  simpa [mul_comm] using phase_mul_star 4

lemma localSpectral_step (r : Fin 4) : localSpectral r = stepMatrix r := by
  fin_cases r
  · exact localSpectral_step_0
  · exact localSpectral_step_1
  · exact localSpectral_step_2
  · exact localSpectral_step_3

lemma localSpectral_operator (r : Fin 4) : matrixOp (localSpectral r) =
    ∑ a : Fin 5, phase (4*(a.val + if 2 ≤ r.val then 1 else 0)) • localProjection r a := by
  simp only [localSpectral, matrixOp, map_sum, map_smul, ← localProjection_eq_matrix]

lemma alice_unitary_matrix (x : Fin 2) :
    (measurementUnitaries (zeta^4) omega_unit alicePVM x : Op H5) =
      matrixOp (stepMatrix (aliceIndex x)) := by
  rw [← localSpectral_step, localSpectral_operator]
  fin_cases x <;>
    simp [measurementUnitaries, relabeled, alicePVM, aliceIndex, localPVM,
      PVM.phaseUnitary, PVM.phase, PVM.eval, PVM.reindex, shiftDown,
      omega_pow_phase, Fin.sum_univ_succ, phase, phaseTable] <;> abel

lemma bob_unitary_matrix (y : Fin 2) :
    (measurementUnitaries (zeta^4) omega_unit bobPVM y : Op H5) =
      matrixOp (stepMatrix (bobIndex y)) := by
  rw [← localSpectral_step, localSpectral_operator]
  fin_cases y <;>
    simp [measurementUnitaries, relabeled, bobPVM, bobIndex, localPVM,
      PVM.phaseUnitary, PVM.phase, PVM.eval, PVM.reindex, shiftDown,
      omega_pow_phase, Fin.sum_univ_succ, phase, phaseTable] <;> abel


def fullAlice (x : Fin 2) : PVM (Op (HTensor H5 H5)) := (alicePVM x).tensorLeft
def fullBob (y : Fin 2) : PVM (Op (HTensor H5 H5)) := (bobPVM y).tensorRight

lemma full_cross_commute (x y : Fin 2) (a b : Fin 5) :
    Commute ((fullAlice x).effect a) ((fullBob y).effect b) :=
  tensorMap_cross_commute _ _

lemma fullAlice_unitary_tensor (x : Fin 2) :
    (measurementUnitaries (zeta^4) omega_unit fullAlice x : Op (HTensor H5 H5)) =
    tensorMap (measurementUnitaries (zeta^4) omega_unit alicePVM x : Op H5) (1 : Op H5) := by
  fin_cases x <;>
    simp [measurementUnitaries, relabeled, fullAlice, PVM.tensorLeft,
      PVM.phaseUnitary, PVM.phase, PVM.eval, PVM.reindex,
      tensorMap_sum_left, tensorMap_smul_left]

lemma fullBob_unitary_tensor (y : Fin 2) :
    (measurementUnitaries (zeta^4) omega_unit fullBob y : Op (HTensor H5 H5)) =
    tensorMap (1 : Op H5) (measurementUnitaries (zeta^4) omega_unit bobPVM y : Op H5) := by
  fin_cases y <;>
    simp [measurementUnitaries, relabeled, fullBob, PVM.tensorRight,
      PVM.phaseUnitary, PVM.phase, PVM.eval, PVM.reindex,
      tensorMap_sum_right, tensorMap_smul_right]

def coordinates : Op (HTensor H5 H5) ≃⋆ₐ[ℂ] Op H25 :=
  (tensorEuclideanEquiv (Fin 5) (Fin 5)).conjStarAlgEquiv

lemma fullAlice_unitary_coordinates (x : Fin 2) :
    coordinates (measurementUnitaries (zeta^4) omega_unit fullAlice x : Op (HTensor H5 H5)) =
      matrixOp (stepMatrix (aliceIndex x) ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ)) := by
  rw [fullAlice_unitary_tensor, alice_unitary_matrix]
  simpa [coordinates, matrixOp] using tensorEuclideanEquiv_operator_kronecker
    (stepMatrix (aliceIndex x)) (1 : Matrix (Fin 5) (Fin 5) ℂ)

lemma fullBob_unitary_coordinates (y : Fin 2) :
    coordinates (measurementUnitaries (zeta^4) omega_unit fullBob y : Op (HTensor H5 H5)) =
      matrixOp ((1 : Matrix (Fin 5) (Fin 5) ℂ) ⊗ₖ stepMatrix (bobIndex y)) := by
  rw [fullBob_unitary_tensor, bob_unitary_matrix]
  simpa [coordinates, matrixOp] using tensorEuclideanEquiv_operator_kronecker
    (1 : Matrix (Fin 5) (Fin 5) ℂ) (stepMatrix (bobIndex y))


lemma kron_one_pow (A : Matrix (Fin 5) (Fin 5) ℂ) (n : ℕ) :
    (A ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ))^n = (A^n) ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
  induction n with
  | zero => simp [Matrix.one_kronecker_one]
  | succ n ih => rw [pow_succ, ih, ← Matrix.mul_kronecker_mul]; simp [pow_succ]

lemma one_kron_pow (A : Matrix (Fin 5) (Fin 5) ℂ) (n : ℕ) :
    ((1 : Matrix (Fin 5) (Fin 5) ℂ) ⊗ₖ A)^n = (1 : Matrix (Fin 5) (Fin 5) ℂ) ⊗ₖ (A^n) := by
  induction n with
  | zero => simp [Matrix.one_kronecker_one]
  | succ n ih => rw [pow_succ, ih, ← Matrix.mul_kronecker_mul]; simp [pow_succ]

lemma word_coordinates (r : Fin 4) (k : ℕ) :
    coordinates (Word.evalStar (measurementUnitaries (zeta^4) omega_unit fullAlice)
      (measurementUnitaries (zeta^4) omega_unit fullBob) (SOS.edgeWord r k)) =
      matrixOp (edgeMatrix r k) := by
  fin_cases r <;>
    simp [Word.evalStar, Word.eval, PartyWord.eval, SOS.edgeWord,
      fullAlice_unitary_coordinates, fullBob_unitary_coordinates]
  all_goals
    simp only [matrixOp, ← map_pow, ← map_mul]
    congr 1
    simp [aliceIndex, bobIndex, edgeMatrix, kron_one_pow, one_kron_pow,
      ← Matrix.mul_kronecker_mul]

/-- The operator from the literal local Fourier strategy is the complete25D matrix Bell operator. -/
lemma sosBell_coordinates :
    coordinates (SOS.bell (zeta^4) (measurementUnitaries (zeta^4) omega_unit fullAlice)
      (measurementUnitaries (zeta^4) omega_unit fullBob)) = matrixOp matrixBell := by
  simp only [SOS.bell, map_sum, map_smul, word_coordinates, matrixBell, matrixOp]

lemma omega_fifth : (zeta^4)^5 = 1 := by
  rw [← pow_mul]
  exact zeta_pow_twenty

lemma omega_geometric : 1 + zeta^4 + (zeta^4)^2 + (zeta^4)^3 + (zeta^4)^4 = 0 := by
  have hp : IsPrimitiveRoot (zeta^4) 5 := zeta_primitive.pow (by norm_num : 0 < 20) (by norm_num : 20 = 4*5)
  have h := hp.geom_sum_eq_zero (by norm_num : 1 < 5)
  simpa [Finset.sum_range_succ] using h

lemma literalBell_coordinates : coordinates (literalBell fullAlice fullBob) = matrixOp matrixBell := by
  rw [← sosBell_eq_literal (zeta^4) omega_unit omega_fifth omega_geometric fullAlice fullBob full_cross_commute]
  exact sosBell_coordinates

end
end CGLMP5.Attainment
