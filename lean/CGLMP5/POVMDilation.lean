import CGLMP5.POVMConstruction
import CGLMP5.POVMConjugate

noncomputable section
open scoped ComplexOrder InnerProductSpace
open ContinuousLinearMap

namespace CGLMP5

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The fixed embedding is independent of the effects and of the measurement setting. -/
def commonJ : H →L[ℂ] DilationSpace H := sumInl

@[simp] theorem commonJ_isometry :
    (commonJ : H →L[ℂ] DilationSpace H).adjoint ∘L commonJ = ContinuousLinearMap.id ℂ H :=
  sumInl_isometry

namespace POVM

/-- The defect completion of the POVM analysis map, as a genuine unitary. -/
def dilationUnitary (E : POVM H) : unitary (Op (DilationSpace H)) :=
  ⟨defectUnitary E.analysis, by
    constructor
    · change (defectUnitary E.analysis).adjoint * defectUnitary E.analysis = 1
      rw [defectUnitary_adjoint, defectUnitary_sq _ E.analysis_isometry]
    · change defectUnitary E.analysis * (defectUnitary E.analysis).adjoint = 1
      rw [defectUnitary_adjoint, defectUnitary_sq _ E.analysis_isometry]⟩

/-- The dilated projective measurement on the same space for every setting. -/
def dilate (E : POVM H) : PVM (Op (DilationSpace H)) :=
  commonCoordinatePVM.unitaryConjugate E.dilationUnitary

@[simp] theorem dilate_effect (E : POVM H) (a : Fin 5) :
    E.dilate.effect a = defectUnitary E.analysis * commonCoordinate a * defectUnitary E.analysis := by
  change (defectUnitary E.analysis).adjoint * commonCoordinate a * defectUnitary E.analysis = _
  rw [defectUnitary_adjoint]

theorem proj_analysis (E : POVM H) (a : Fin 5) :
    PiLp.proj 2 (fun _ : Fin 5 => H) a ∘L E.analysis = E.sqrtEffect a := by
  ext h
  rfl

theorem analysis_adjoint_coordInl (E : POVM H) (a : Fin 5) :
    E.analysis.adjoint ∘L coordInl a = (E.sqrtEffect a).adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (E.proj_analysis a)
  simpa only [adjoint_comp, ← coordInl_adjoint, adjoint_adjoint] using h

/-- Each original effect is the compression of the matching coordinate projection. -/
theorem analysis_compression (E : POVM H) (a : Fin 5) :
    E.analysis.adjoint ∘L coordProjection a ∘L E.analysis = E.effect a := by
  change E.analysis.adjoint ∘L (coordInl a ∘L PiLp.proj 2 (fun _ : Fin 5 => H) a) ∘L
    E.analysis = _
  simp only [comp_assoc]
  rw [E.proj_analysis, ← comp_assoc, E.analysis_adjoint_coordInl]
  exact E.sqrtEffect_star_mul a

/-- The same inclusion J compresses every dilated effect to the original effect. -/
@[simp] theorem dilate_compression (E : POVM H) (a : Fin 5) :
    compression commonJ (E.dilate.effect a) = E.effect a := by
  apply ContinuousLinearMap.ext
  intro h
  change (commonJ : H →L[ℂ] DilationSpace H).adjoint (E.dilate.effect a (commonJ h)) = _
  rw [dilate_effect]
  simp only [commonJ, sumInl_adjoint, mul_apply_eq_comp, sumInl_apply]
  simp only [defectUnitary_apply, map_zero, add_zero, commonCoordinate_apply, ite_self,
    sumFst_apply]
  exact congrArg (fun T : Op H => T h) (E.analysis_compression a)

end POVM

/-- Simultaneous local dilation: a single space and one fixed J work for both settings. -/
theorem common_dilation (E : Fin 2 → POVM H) :
    ∃ P : Fin 2 → PVM (Op (DilationSpace H)),
      ∀ x a, compression (commonJ : H →L[ℂ] DilationSpace H) ((P x).effect a) = (E x).effect a :=
  ⟨fun x => (E x).dilate, fun x a => (E x).dilate_compression a⟩

end CGLMP5
