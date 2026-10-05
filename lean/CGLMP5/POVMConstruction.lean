import CGLMP5.POVM

noncomputable section
open scoped ComplexOrder InnerProductSpace
open ContinuousLinearMap

namespace CGLMP5

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The same fivefold Hilbert sum is used for every local measurement setting. -/
abbrev DilationAux (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  PiLp 2 (fun _ : Fin 5 => H)

abbrev DilationSpace (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  HilbertSum H (DilationAux H)

namespace POVM

/-- Positive bounded square roots exist in every Hilbert dimension. -/
theorem exists_sqrtEffect (E : POVM H) (a : Fin 5) :
    ∃ S : Op H, IsSelfAdjoint S ∧ S * S = E.effect a := by
  have hp := ContinuousLinearMap.nonneg_iff_isPositive.mp (E.nonneg a)
  obtain ⟨S, hS, _, hSq⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hp.isSelfAdjoint hp.spectrumRestricts
  exact ⟨S, hS, hSq⟩

/-- A square-root factor selected using the continuous functional calculus. -/
def sqrtEffect (E : POVM H) (a : Fin 5) : Op H := (E.exists_sqrtEffect a).choose

theorem sqrtEffect_selfadjoint (E : POVM H) (a : Fin 5) :
    IsSelfAdjoint (E.sqrtEffect a) := (E.exists_sqrtEffect a).choose_spec.1

theorem sqrtEffect_square (E : POVM H) (a : Fin 5) :
    E.sqrtEffect a * E.sqrtEffect a = E.effect a := (E.exists_sqrtEffect a).choose_spec.2

@[simp] theorem sqrtEffect_star_mul (E : POVM H) (a : Fin 5) :
    star (E.sqrtEffect a) * E.sqrtEffect a = E.effect a := by
  rw [(E.sqrtEffect_selfadjoint a).star_eq, E.sqrtEffect_square]

/-- The usual Naimark analysis map into five copies of the original Hilbert space. -/
def analysis (E : POVM H) : H →L[ℂ] DilationAux H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 5 => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi E.sqrtEffect

@[simp] theorem analysis_apply (E : POVM H) (h : H) (a : Fin 5) :
    E.analysis h a = E.sqrtEffect a h := rfl

theorem analysis_inner (E : POVM H) (x y : H) :
    inner ℂ (E.analysis x) (E.analysis y) = inner ℂ x y := by
  rw [PiLp.inner_apply]
  calc
    (∑ a, inner ℂ (E.analysis x a) (E.analysis y a)) =
        ∑ a, inner ℂ x (E.effect a y) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [analysis_apply, analysis_apply, ← adjoint_inner_right]
      have h := congrArg (fun T : Op H => T y) (E.sqrtEffect_star_mul a)
      exact congrArg (inner ℂ x) h
    _ = inner ℂ x ((∑ a, E.effect a) y) := by simp [sum_apply, inner_sum]
    _ = inner ℂ x y := by rw [E.sum_one]; rfl

@[simp] theorem analysis_isometry (E : POVM H) :
    E.analysis.adjoint ∘L E.analysis = ContinuousLinearMap.id ℂ H := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y (E.analysis.adjoint (E.analysis x)) = inner ℂ y x
  rw [adjoint_inner_right, E.analysis_inner]

end POVM

/-- Coordinate inclusion into the fivefold Hilbert sum. -/
def coordInl (a : Fin 5) : H →L[ℂ] DilationAux H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 5 => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : Fin 5 => H) a

@[simp] theorem coordInl_apply (a : Fin 5) (h : H) :
    coordInl a h = PiLp.single 2 a h := rfl

@[simp] theorem coordInl_adjoint (a : Fin 5) :
    (coordInl a : H →L[ℂ] DilationAux H).adjoint = PiLp.proj 2 (fun _ : Fin 5 => H) a := by
  symm
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (x a) y = inner ℂ x (PiLp.single 2 a y)
  rw [PiLp.inner_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- The coordinate PVM on the fivefold Hilbert sum. -/
def coordProjection (a : Fin 5) : Op (DilationAux H) :=
  coordInl a ∘L PiLp.proj 2 (fun _ : Fin 5 => H) a

@[simp] theorem coordProjection_apply (a : Fin 5) (v : DilationAux H) :
    coordProjection a v = PiLp.single 2 a (v a) := rfl

@[simp] theorem coordProjection_selfadjoint (a : Fin 5) :
    star (coordProjection a : Op (DilationAux H)) = coordProjection a := by
  change (coordInl a ∘L PiLp.proj 2 (fun _ : Fin 5 => H) a).adjoint = _
  rw [adjoint_comp, ← coordInl_adjoint, adjoint_adjoint, coordInl_adjoint]
  rfl


theorem coordProjection_mul (a b : Fin 5) :
    (coordProjection a : Op (DilationAux H)) * coordProjection b =
      if a = b then coordProjection a else 0 := by
  by_cases h : a = b
  · subst b
    apply ContinuousLinearMap.ext
    intro v
    simp [coordProjection_apply]
  · apply ContinuousLinearMap.ext
    intro v
    simp [coordProjection_apply, h]

@[simp] theorem coordProjection_apply_apply (a b : Fin 5) (v : DilationAux H) :
    coordProjection a v b = if b = a then v a else 0 := by
  by_cases h : b = a <;> simp [coordProjection_apply, h]

theorem coordProjection_sum : (∑ a, (coordProjection a : Op (DilationAux H))) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro b
  change (PiLp.proj 2 (fun _ : Fin 5 => H) b : DilationAux H →L[ℂ] H)
    ((∑ a, coordProjection a) v) = v b
  rw [sum_apply, map_sum]
  change (∑ a, coordProjection a v b) = v b
  simp only [coordProjection_apply_apply]
  simp

/-- The coordinate projections, assigning the additional H summand to outcome zero. -/
def commonCoordinate (a : Fin 5) : Op (DilationSpace H) :=
  block (if a = 0 then 1 else 0) 0 0 (coordProjection a)

@[simp] theorem commonCoordinate_apply (a : Fin 5) (h : H) (v : DilationAux H) :
    commonCoordinate a (WithLp.toLp 2 (h,v)) =
      WithLp.toLp 2 (if a = 0 then h else 0, coordProjection a v) := by
  by_cases ha : a = 0 <;> simp [commonCoordinate, ha]

theorem commonCoordinate_selfadjoint (a : Fin 5) :
    star (commonCoordinate a : Op (DilationSpace H)) = commonCoordinate a := by
  change (commonCoordinate a).adjoint = commonCoordinate a
  symm
  apply (eq_adjoint_iff _ _).mpr
  rintro ⟨h,v⟩ ⟨h',v'⟩
  change inner ℂ (commonCoordinate a (WithLp.toLp 2 (h,v))) (WithLp.toLp 2 (h',v')) =
    inner ℂ (WithLp.toLp 2 (h,v)) (commonCoordinate a (WithLp.toLp 2 (h',v')))
  have hc : inner ℂ (coordProjection a v) v' = inner ℂ v (coordProjection a v') := by
    rw [← adjoint_inner_right]
    change inner ℂ v (star (coordProjection a) v') = _
    rw [coordProjection_selfadjoint]
  simp only [commonCoordinate_apply, WithLp.prod_inner_apply, hc]
  by_cases ha : a = 0 <;> simp only [ha, ite_true, ite_false, inner_zero_left, inner_zero_right]

theorem commonCoordinate_mul (a b : Fin 5) :
    (commonCoordinate a : Op (DilationSpace H)) * commonCoordinate b =
      if a = b then commonCoordinate a else 0 := by
  apply ContinuousLinearMap.ext
  rintro ⟨h,v⟩
  have hc := congrArg (fun T : Op (DilationAux H) => T v) (coordProjection_mul (H := H) a b)
  change coordProjection a (coordProjection b v) = _ at hc
  change commonCoordinate a (commonCoordinate b (WithLp.toLp 2 (h,v))) = _
  by_cases hab : a = b
  · subst b
    simp only [ite_true] at hc ⊢
    simp only [commonCoordinate_apply, hc]
    by_cases ha : a = 0 <;> simp only [ha, ite_true, ite_false]
  · have hzero : ¬ (a = 0 ∧ b = 0) := by rintro ⟨rfl,rfl⟩; exact hab rfl
    simp only [if_neg hab, zero_apply] at hc ⊢
    rw [commonCoordinate_apply, commonCoordinate_apply, hc]
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all

theorem commonCoordinate_sum : (∑ a, (commonCoordinate a : Op (DilationSpace H))) = 1 := by
  apply ContinuousLinearMap.ext
  rintro ⟨h,v⟩
  change (∑ a, commonCoordinate a (WithLp.toLp 2 (h,v))) = WithLp.toLp 2 (h,v)
  simp only [commonCoordinate_apply]
  apply (WithLp.linearEquiv 2 ℂ (H × DilationAux H)).injective
  rw [map_sum]
  change (∑ a : Fin 5, (if a = 0 then h else 0, coordProjection a v)) = (h,v)
  apply Prod.ext
  · simp only [Prod.fst_sum]
    change (∑ a : Fin 5, if a = 0 then h else 0) = h
    simp
  · simpa only [Prod.snd_sum, sum_apply, Prod.snd, one_apply_eq_self] using
      congrArg (fun T : Op (DilationAux H) => T v) (coordProjection_sum (H := H))

/-- A common-space coordinate PVM, chosen independently of all POVM effects. -/
def commonCoordinatePVM : PVM (Op (DilationSpace H)) where
  effect := commonCoordinate
  selfadjoint := commonCoordinate_selfadjoint
  mul_eq := commonCoordinate_mul
  sum_one := commonCoordinate_sum

end CGLMP5
