import CGLMP5.AttainmentFourier

namespace CGLMP5.Attainment
noncomputable section

def aliceIndex (x : Fin 2) : Fin 4 := ⟨2*x.val, by omega⟩
def bobIndex (y : Fin 2) : Fin 4 := ⟨2*y.val+1, by omega⟩

def alpha (x : Fin 2) : ℝ := (x.val : ℝ) / 2
def beta (y : Fin 2) : ℝ := 1/4 - (y.val : ℝ)/2

lemma alpha_values : alpha 0 = 0 ∧ alpha 1 = 1/2 := by norm_num [alpha]
lemma beta_values : beta 0 = 1/4 ∧ beta 1 = -(1/4) := by norm_num [beta]

lemma phase_eq_exp (n : ℕ) : phase n =
    Complex.exp ((n : ℂ) * ((Real.pi/10 : ℝ) : ℂ) * Complex.I) := by
  rw [phase_eq_pow, zeta_eq_exp, ← Complex.exp_nat_mul]
  congr 1
  ring

lemma fourierAmplitude : (s : ℂ)/5 = 1/(Real.sqrt 5 : ℂ) := by
  change (s : ℂ)/5 = 1/(s : ℂ)
  have hs : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
  have hn : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt s_pos)
  apply (eq_div_iff hn).2
  linear_combination (1/5 : ℂ)*hs

/-- The literal standard Alice Fourier vectors with offsets (0,1/2). -/
lemma alice_fourier_formula (x : Fin 2) (a j : Fin 5) :
    fourierVector (aliceIndex x) a j =
      (1/(Real.sqrt 5 : ℂ)) * Complex.exp
        ((((2*Real.pi*(j.val : ℝ)*((a.val : ℝ)+alpha x)/5) : ℝ) : ℂ) * Complex.I) := by
  change (s : ℂ)/5 * phase (phaseExponent (aliceIndex x) a j) = _
  rw [fourierAmplitude, phase_eq_exp]
  congr 1
  congr 1
  fin_cases x <;> simp [aliceIndex, phaseExponent, alpha] <;> push_cast <;> ring

/-- The literal standard Bob Fourier vectors with offsets (1/4,-1/4), including -b. -/
lemma bob_fourier_formula (y : Fin 2) (b j : Fin 5) :
    fourierVector (bobIndex y) b j =
      (1/(Real.sqrt 5 : ℂ)) * Complex.exp
        ((((2*Real.pi*(j.val : ℝ)*(-(b.val : ℝ)+beta y)/5) : ℝ) : ℂ) * Complex.I) := by
  change (s : ℂ)/5 * phase (phaseExponent (bobIndex y) b j) = _
  rw [fourierAmplitude, phase_eq_exp]
  have he : (phaseExponent (bobIndex y) b j : ℂ) * ((Real.pi/10 : ℝ) : ℂ) * Complex.I =
      ((((2*Real.pi*(j.val : ℝ)*(-(b.val : ℝ)+beta y)/5) : ℝ) : ℂ) * Complex.I) +
      (j.val : ℂ) * (2*(Real.pi : ℂ)*Complex.I) := by
    fin_cases y <;> fin_cases b <;>
      simp [bobIndex, phaseExponent, beta] <;> push_cast <;> ring
  rw [he, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

end
end CGLMP5.Attainment
