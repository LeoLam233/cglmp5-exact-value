import CGLMP5.Operator
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! # An explicit fixed-common-space Naimark dilation

The block operator is built using the defect of an arbitrary isometry, never its
surjectivity. Both local settings use exactly the same inclusion into the same space.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open ContinuousLinearMap

namespace CGLMP5

abbrev HilbertSum (H M : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M] := WithLp 2 (H × M)

variable {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

/-- The left coordinate inclusion, independent of any measurement. -/
def sumInl : H →L[ℂ] HilbertSum H M :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H M).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl ℂ H M

/-- The first coordinate projection. -/
def sumFst : HilbertSum H M →L[ℂ] H :=
  ContinuousLinearMap.fst ℂ H M ∘L (WithLp.prodContinuousLinearEquiv 2 ℂ H M).toContinuousLinearMap

/-- The second coordinate projection. -/
def sumSnd : HilbertSum H M →L[ℂ] M :=
  ContinuousLinearMap.snd ℂ H M ∘L (WithLp.prodContinuousLinearEquiv 2 ℂ H M).toContinuousLinearMap

@[simp] theorem sumInl_apply (h : H) : sumInl (M := M) h = WithLp.toLp 2 (h, 0) := rfl
@[simp] theorem sumFst_apply (h : H) (m : M) : sumFst (WithLp.toLp 2 (h, m)) = h := rfl
@[simp] theorem sumSnd_apply (h : H) (m : M) : sumSnd (WithLp.toLp 2 (h, m)) = m := rfl

@[simp] theorem sumInl_adjoint : (sumInl : H →L[ℂ] HilbertSum H M).adjoint = sumFst := by
  symm
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  simp [sumFst, sumInl, WithLp.prod_inner_apply]

@[simp] theorem sumInl_isometry :
    (sumInl : H →L[ℂ] HilbertSum H M).adjoint ∘L sumInl = ContinuousLinearMap.id ℂ H := by
  ext h
  simp

/-- A bounded block operator on a Hilbert direct sum. -/
def block (A : Op H) (B : M →L[ℂ] H) (C : H →L[ℂ] M) (D : Op M) : Op (HilbertSum H M) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H M).symm.toContinuousLinearMap ∘L
    ((A ∘L sumFst + B ∘L sumSnd).prod (C ∘L sumFst + D ∘L sumSnd))

@[simp] theorem block_apply (A : Op H) (B : M →L[ℂ] H) (C : H →L[ℂ] M) (D : Op M)
    (h : H) (m : M) :
    block A B C D (WithLp.toLp 2 (h, m)) = WithLp.toLp 2 (A h + B m, C h + D m) := rfl

/-- The defect projection of an isometry into a possibly larger Hilbert space. -/
def defect (V : H →L[ℂ] M) : Op M := 1 - V ∘L V.adjoint

@[simp] theorem defect_adjoint (V : H →L[ℂ] M) : (defect V).adjoint = defect V := by
  simp [defect, adjoint_one]

theorem defect_comp (V : H →L[ℂ] M) (hV : V.adjoint ∘L V = ContinuousLinearMap.id ℂ H) :
    defect V ∘L V = 0 := by
  simp only [defect, sub_comp, comp_assoc, hV, comp_id]
  change V - V = 0
  simp

theorem adjoint_comp_defect (V : H →L[ℂ] M)
    (hV : V.adjoint ∘L V = ContinuousLinearMap.id ℂ H) : V.adjoint ∘L defect V = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint (defect_comp V hV)
  simpa using h

theorem defect_sq (V : H →L[ℂ] M) (hV : V.adjoint ∘L V = ContinuousLinearMap.id ℂ H) :
    defect V ∘L defect V = defect V := by
  change defect V ∘L (1 - V ∘L V.adjoint) = defect V
  rw [comp_sub, ← comp_assoc, defect_comp V hV, zero_comp, sub_zero]
  rfl

/-- The self-adjoint defect unitary completing any isometry. -/
def defectUnitary (V : H →L[ℂ] M) : Op (HilbertSum H M) :=
  block 0 V.adjoint V (defect V)

@[simp] theorem defectUnitary_apply (V : H →L[ℂ] M) (h : H) (m : M) :
    defectUnitary V (WithLp.toLp 2 (h, m)) = WithLp.toLp 2 (V.adjoint m, V h + defect V m) := by
  simp [defectUnitary]

/-- The block construction is genuinely self-adjoint. -/
theorem defectUnitary_adjoint (V : H →L[ℂ] M) : (defectUnitary V).adjoint = defectUnitary V := by
  symm
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  obtain ⟨h, m⟩ := x
  obtain ⟨h', m'⟩ := y
  change inner ℂ (defectUnitary V (WithLp.toLp 2 (h,m))) (WithLp.toLp 2 (h',m')) =
    inner ℂ (WithLp.toLp 2 (h,m)) (defectUnitary V (WithLp.toLp 2 (h',m')))
  have hd : inner ℂ (defect V m) m' = inner ℂ m (defect V m') := by
    rw [← adjoint_inner_right, defect_adjoint]
  simp only [defectUnitary_apply, WithLp.prod_inner_apply, WithLp.ofLp_toLp,
    inner_add_left, inner_add_right, adjoint_inner_left, adjoint_inner_right, hd]
  exact add_left_comm _ _ _

theorem defectUnitary_sq (V : H →L[ℂ] M)
    (hV : V.adjoint ∘L V = ContinuousLinearMap.id ℂ H) :
    defectUnitary V * defectUnitary V = 1 := by
  apply ContinuousLinearMap.ext
  rintro ⟨h, m⟩
  change defectUnitary V (defectUnitary V (WithLp.toLp 2 (h,m))) = WithLp.toLp 2 (h,m)
  have h₁ : V.adjoint (V h) = h := congrArg (fun T : Op H => T h) hV
  have h₂ : V.adjoint (defect V m) = 0 :=
    congrArg (fun T : M →L[ℂ] H => T m) (adjoint_comp_defect V hV)
  have h₃ : defect V (V h) = 0 :=
    congrArg (fun T : H →L[ℂ] M => T h) (defect_comp V hV)
  have h₄ : defect V (defect V m) = defect V m :=
    congrArg (fun T : Op M => T m) (defect_sq V hV)
  simp only [mul_apply, defectUnitary_apply, map_add, h₁, h₂, h₃, h₄, add_zero, zero_add,
    one_apply_eq_self]
  congr 1
  simp [defect]

end CGLMP5
