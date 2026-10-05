import CGLMP5.POVMTransfer

/-! # Transport under arbitrary local Hilbert-space equivalences

This includes universe lifts via `LinearIsometryEquiv.ulift.symm`, and preserves the actual
joint probability table. It does not add an artificial value to the strategy value set.
-/

noncomputable section
open scoped ComplexOrder
open ContinuousLinearMap

namespace CGLMP5

variable {H K H' K' : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

@[simp] theorem equiv_isometry (e : H ≃ₗᵢ[ℂ] H') :
    (e : H →L[ℂ] H').adjoint ∘L (e : H →L[ℂ] H') = ContinuousLinearMap.id ℂ H := by
  rw [e.adjoint_eq_symm]
  ext x
  simp

/-- Conjugation of a local POVM by a Hilbert-space equivalence. -/
def POVM.transport (E : POVM H) (e : H ≃ₗᵢ[ℂ] H') : POVM H' where
  effect a := compression (e.symm : H' →L[ℂ] H) (E.effect a)
  nonneg a := (compression _).map_nonneg (E.nonneg a)
  sum_one := by
    rw [← map_sum, E.sum_one, compression_one _ (equiv_isometry e.symm)]

@[simp] theorem POVM.transport_compression (E : POVM H) (e : H ≃ₗᵢ[ℂ] H') (a : Fin 5) :
    compression (e : H →L[ℂ] H') ((E.transport e).effect a) = E.effect a := by
  apply ContinuousLinearMap.ext
  intro x
  change (e : H →L[ℂ] H').adjoint ((e.symm : H' →L[ℂ] H).adjoint
    (E.effect a (e.symm (e x)))) = E.effect a x
  rw [e.adjoint_eq_symm, e.symm.adjoint_eq_symm]
  simp

/-- Joint-state transport using the same local equivalences for every measurement setting. -/
def transportState (φ : State (HTensor H K)) (e : H ≃ₗᵢ[ℂ] H') (f : K ≃ₗᵢ[ℂ] K') :
    State (HTensor H' K') :=
  φ.pullback (tensorMap (e : H →L[ℂ] H') (f : K →L[ℂ] K'))
    (tensorMap_isometry _ _ (equiv_isometry e) (equiv_isometry f))

@[simp] theorem jointProbability_transport (φ : State (HTensor H K))
    (A : Setting → POVM H) (B : Setting → POVM K)
    (e : H ≃ₗᵢ[ℂ] H') (f : K ≃ₗᵢ[ℂ] K') (x y : Setting) (a b : Outcome) :
    jointProbability (transportState φ e f) (fun x => (A x).transport e)
      (fun y => (B y).transport f) x y a b = jointProbability φ A B x y a b := by
  change (φ.pullback (tensorMap (e : H →L[ℂ] H') (f : K →L[ℂ] K')) _).expect
    (tensorMap (((A x).transport e).effect a) (((B y).transport f).effect b)) = _
  rw [State.pullback_expect, tensor_compression, POVM.transport_compression, POVM.transport_compression]
  rfl

@[simp] theorem cglmp_transport (φ : State (HTensor H K))
    (A : Setting → POVM H) (B : Setting → POVM K)
    (e : H ≃ₗᵢ[ℂ] H') (f : K ≃ₗᵢ[ℂ] K') :
    cglmp (jointProbability (transportState φ e f) (fun x => (A x).transport e)
      (fun y => (B y).transport f)) = cglmp (jointProbability φ A B) := by
  congr 1
  funext x y a b
  exact jointProbability_transport φ A B e f x y a b

end CGLMP5
