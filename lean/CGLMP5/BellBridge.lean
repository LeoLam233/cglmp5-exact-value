import CGLMP5.Fourier

namespace CGLMP5

private theorem coeff00 : ∀ a b : Fin 5,
    eventCoefficientTwo 0 0 a b = 2-(↑((a.val+10-b.val)%5):Int) := by decide
private theorem coeff10 : ∀ a b : Fin 5,
    eventCoefficientTwo 1 0 a b = 2-(↑((b.val+10-(shiftDown.symm a).val)%5):Int) := by decide
private theorem coeff11 : ∀ a b : Fin 5,
    eventCoefficientTwo 1 1 a b =
      2-(↑(((shiftDown.symm a).val+10-(shiftDown.symm b).val)%5):Int) := by decide
private theorem coeff01 : ∀ a b : Fin 5,
    eventCoefficientTwo 0 1 a b = 2-(↑(((shiftDown.symm b).val+10-a.val-1)%5):Int) := by decide

private theorem complex_coeff {c : Int} {n : Nat} (h : c = 2-(n:Int)) :
    (c:ℂ) = 2-(n:ℂ) := by exact_mod_cast h

section Operators
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

noncomputable def literalBell (A B : Fin 2 → PVM R) : R :=
  ∑ x, ∑ y, ∑ a, ∑ b, ((eventCoefficientTwo x y a b:ℂ)/2) •
    ((A x).effect a * (B y).effect b)

noncomputable def cyclicBell (ω : ℂ) (A B : Fin 2 → PVM R) : R :=
  pairBell ω (A 0) (B 0) 0 +
  pairBell ω (B 0) ((A 1).reindex shiftDown) 0 +
  pairBell ω ((A 1).reindex shiftDown) ((B 1).reindex shiftDown) 0 +
  pairBell ω ((B 1).reindex shiftDown) (A 0) 1

@[simp] theorem PVM.reindex_refl (P : PVM R) : P.reindex (Equiv.refl _) = P := by
  cases P
  rfl

/-- Source-to-operator bridge for every bounded or abstract complex star representation. -/
theorem cyclicBell_eq_literal (ω : ℂ) (hω : ω^5=1)
    (hc : 1+ω+ω^2+ω^3+ω^4=0) (A B : Fin 2 → PVM R)
    (hcomm : ∀ x y a b, Commute ((A x).effect a) ((B y).effect b)) :
    cyclicBell ω A B = literalBell A B := by
  have h00 : pairBell ω (A 0) (B 0) 0 =
      ∑ a, ∑ b, ((eventCoefficientTwo 0 0 a b:ℂ)/2) • ((A 0).effect a*(B 0).effect b) := by
    rw [pairBell_eq ω hω hc]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [complex_coeff (coeff00 a b)]
    rfl
  have h10 : pairBell ω (B 0) ((A 1).reindex shiftDown) 0 =
      ∑ a, ∑ b, ((eventCoefficientTwo 1 0 a b:ℂ)/2) • ((A 1).effect a*(B 0).effect b) := by
    have h := pairBell_reindex ω hω hc (B 0) (A 1) (Equiv.refl _) shiftDown 0
    simp only [PVM.reindex_refl, Equiv.refl_symm, Equiv.refl_apply] at h
    rw [h, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [complex_coeff (coeff10 a b), (hcomm 1 0 a b).eq]
    rfl
  have h11 : pairBell ω ((A 1).reindex shiftDown) ((B 1).reindex shiftDown) 0 =
      ∑ a, ∑ b, ((eventCoefficientTwo 1 1 a b:ℂ)/2) • ((A 1).effect a*(B 1).effect b) := by
    rw [pairBell_reindex ω hω hc]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [complex_coeff (coeff11 a b)]
    rfl
  have h01 : pairBell ω ((B 1).reindex shiftDown) (A 0) 1 =
      ∑ a, ∑ b, ((eventCoefficientTwo 0 1 a b:ℂ)/2) • ((A 0).effect a*(B 1).effect b) := by
    have h := pairBell_reindex ω hω hc (B 1) (A 0) shiftDown (Equiv.refl _) 1
    simp only [PVM.reindex_refl, Equiv.refl_symm, Equiv.refl_apply] at h
    rw [h, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [complex_coeff (coeff01 a b), (hcomm 0 1 a b).eq]
    rfl
  simp only [cyclicBell, h00, h10, h11, h01, literalBell, Fin.sum_univ_two]
  abel

/-- The manuscript's outcome relabelling D2=A1+1, D3=B1+1. -/
noncomputable def relabeled (P : Fin 2 → PVM R) (x : Fin 2) : PVM R :=
  if x.val=0 then P 0 else (P 1).reindex shiftDown

noncomputable def measurementUnitaries (ω : ℂ) (hunit : star ω*ω=1)
    (P : Fin 2 → PVM R) (x : Fin 2) : unitary R :=
  (relabeled P x).phaseUnitary ω hunit

theorem measurementUnitaries_fifth (ω : ℂ) (hunit : star ω*ω=1) (hω : ω^5=1)
    (P : Fin 2 → PVM R) (x : Fin 2) : measurementUnitaries ω hunit P x ^5=1 := by
  apply Subtype.ext
  exact (relabeled P x).phase_fifth ω hω

theorem measurementUnitaries_commute (ω : ℂ) (hunit : star ω*ω=1)
    (A B : Fin 2 → PVM R)
    (hcomm : ∀ x y a b, Commute ((A x).effect a) ((B y).effect b)) (x y : Fin 2) :
    Commute (measurementUnitaries ω hunit A x) (measurementUnitaries ω hunit B y) := by
  change _ * _ = _ * _
  apply Subtype.ext
  change Commute ((relabeled A x).phase ω) ((relabeled B y).phase ω)
  apply PVM.phase_commute
  intro a b
  fin_cases x <;> fin_cases y <;>
    simp only [relabeled, Fin.val_zero, Fin.val_one, ite_true, Nat.one_ne_zero, ite_false,
      PVM.reindex] <;> apply hcomm

theorem sosBell_eq_cyclic (ω : ℂ) (hunit : star ω*ω=1)
    (A B : Fin 2 → PVM R)
    (hcomm : ∀ x y a b, Commute ((A x).effect a) ((B y).effect b)) :
    SOS.bell ω (measurementUnitaries ω hunit A) (measurementUnitaries ω hunit B) =
      cyclicBell ω A B := by
  have hab x y : Commute ((relabeled A x).phase ω) ((relabeled B y).phase ω) := by
    have h := measurementUnitaries_commute ω hunit A B hcomm x y
    exact congrArg Subtype.val h.eq
  have h10 m n := ((hab 1 0).pow_pow m n).eq
  have h01 m n := ((hab 0 1).pow_pow m n).eq
  have h10L := ((hab 1 0).pow_left 4).eq
  have h10R := ((hab 1 0).pow_right 4).eq
  have h01L := ((hab 0 1).pow_left 4).eq
  have h01R := ((hab 0 1).pow_right 4).eq
  simp only [relabeled, Fin.val_zero, Fin.val_one, ite_true, Nat.one_ne_zero, ite_false] at h10 h01 h10L h10R h01L h01R
  simp [SOS.bell, Fin.sum_univ_four, SOS.edgeCoefficient, SOS.edgeWord,
    Word.evalStar, Word.eval, PartyWord.eval, measurementUnitaries, PVM.phaseUnitary,
    relabeled, cyclicBell, pairBell, h10, h01, h10L, h10R, h01L, h01R]

/-- The compact SOS target is the literal published probability functional's Bell operator. -/
theorem sosBell_eq_literal (ω : ℂ) (hunit : star ω*ω=1) (hω : ω^5=1)
    (hc : 1+ω+ω^2+ω^3+ω^4=0) (A B : Fin 2 → PVM R)
    (hcomm : ∀ x y a b, Commute ((A x).effect a) ((B y).effect b)) :
    SOS.bell ω (measurementUnitaries ω hunit A) (measurementUnitaries ω hunit B) =
      literalBell A B :=
  (sosBell_eq_cyclic ω hunit A B hcomm).trans (cyclicBell_eq_literal ω hω hc A B hcomm)


end Operators
end CGLMP5
