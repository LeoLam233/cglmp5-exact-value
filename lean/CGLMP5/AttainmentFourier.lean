import CGLMP5.AttainmentOverlap
import CGLMP5.Measurements
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace CGLMP5.Attainment
noncomputable section
open scoped BigOperators

def fourierVector (r : Fin 4) (a : Fin 5) : EuclideanSpace ℂ (Fin 5) :=
  WithLp.toLp 2 (fun j => (s : ℂ) / 5 * phase (phaseExponent r a j))

lemma fourier_inner (r : Fin 4) (a b : Fin 5) :
    inner ℂ (fourierVector r a) (fourierVector r b) = if a = b then 1 else 0 := by
  have hs : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
  simp only [PiLp.inner_apply, fourierVector, RCLike.inner_apply', ← Complex.star_def]
  have h : (∑ j : Fin 5, star ((s : ℂ) / 5 * phase (phaseExponent r a j)) *
      ((s : ℂ) / 5 * phase (phaseExponent r b j))) =
      ((s : ℂ)^2 / 25) *
        (∑ j : Fin 5, star (phase (phaseExponent r a j)) * phase (phaseExponent r b j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [star_mul, star_div₀, Complex.star_def, map_ofNat, Complex.conj_ofReal]
    ring
  rw [h, phase_overlap, hs]
  split_ifs <;> norm_num

lemma fourier_orthonormal (r : Fin 4) : Orthonormal ℂ (fourierVector r) := by
  rw [orthonormal_iff_ite]
  exact fourier_inner r

noncomputable def fourierBasis (r : Fin 4) : OrthonormalBasis (Fin 5) ℂ (EuclideanSpace ℂ (Fin 5)) :=
  (basisOfOrthonormalOfCardEqFinrank (fourier_orthonormal r) (by simp)).toOrthonormalBasis
    (by simpa using fourier_orthonormal r)

lemma fourierBasis_apply (r : Fin 4) (a : Fin 5) : fourierBasis r a = fourierVector r a := by
  simp [fourierBasis]

def localProjection (r : Fin 4) (a : Fin 5) :
    EuclideanSpace ℂ (Fin 5) →L[ℂ] EuclideanSpace ℂ (Fin 5) :=
  InnerProductSpace.rankOne ℂ (fourierVector r a) (fourierVector r a)

lemma localProjection_positive (r : Fin 4) (a : Fin 5) :
    (localProjection r a).IsPositive := InnerProductSpace.isPositive_rankOne_self _

lemma localProjection_selfadjoint (r : Fin 4) (a : Fin 5) :
    star (localProjection r a) = localProjection r a := by
  simp [localProjection, ContinuousLinearMap.star_eq_adjoint]

lemma localProjection_mul (r : Fin 4) (a b : Fin 5) :
    localProjection r a * localProjection r b = if a = b then localProjection r a else 0 := by
  simp only [localProjection, ContinuousLinearMap.mul_def,
    InnerProductSpace.rankOne_comp_rankOne, fourier_inner]
  split_ifs with h
  · subst b; simp
  · simp

lemma localProjection_sum (r : Fin 4) : ∑ a, localProjection r a = 1 := by
  have h := (fourierBasis r).sum_rankOne_eq_id
  change (∑ a, localProjection r a) = ContinuousLinearMap.id ℂ _
  simpa only [fourierBasis_apply, localProjection] using h

/-- The four actual five-outcome projective measurements. -/
def localPVM (r : Fin 4) : PVM (EuclideanSpace ℂ (Fin 5) →L[ℂ] EuclideanSpace ℂ (Fin 5)) where
  effect := localProjection r
  selfadjoint := localProjection_selfadjoint r
  mul_eq := localProjection_mul r
  sum_one := localProjection_sum r

end
end CGLMP5.Attainment
