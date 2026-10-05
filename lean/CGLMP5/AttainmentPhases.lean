import CGLMP5.Root
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push

namespace CGLMP5.Attainment
noncomputable section
open Complex

/-- A complete algebraic table for exp(k*pi*i/10), with no numerical entries. -/
def phaseTable (R U : ℂ) : Fin 20 → ℂ :=
  ![1,
    Complex.I*R/4 - Complex.I/4 + U/4,
    Complex.I*R*U/8 - Complex.I*U/8 + R/4 + 1/4,
    Complex.I*R/4 + Complex.I/4 + R*U/8 - U/8,
    Complex.I*U/4 + R/4 - 1/4,
    Complex.I,
    Complex.I*U/4 - R/4 + 1/4,
    Complex.I*R/4 + Complex.I/4 - R*U/8 + U/8,
    Complex.I*R*U/8 - Complex.I*U/8 - R/4 - 1/4,
    Complex.I*R/4 - Complex.I/4 - U/4,
    -1,
    -Complex.I*R/4 + Complex.I/4 - U/4,
    -Complex.I*R*U/8 + Complex.I*U/8 - R/4 - 1/4,
    -Complex.I*R/4 - Complex.I/4 - R*U/8 + U/8,
    -Complex.I*U/4 - R/4 + 1/4,
    -Complex.I,
    -Complex.I*U/4 + R/4 - 1/4,
    -Complex.I*R/4 - Complex.I/4 + R*U/8 - U/8,
    -Complex.I*R*U/8 + Complex.I*U/8 + R/4 + 1/4,
    -Complex.I*R/4 + Complex.I/4 + U/4]

theorem phaseTable_step (R U : ℂ) (hs : R^2 = 5) (hu : U^2 = 10 + 2*R)
    (k : Fin 20) :
    phaseTable R U ⟨(k.val+1)%20, Nat.mod_lt _ (by omega)⟩ =
      phaseTable R U k * ((U + Complex.I*(R-1))/4) := by
  have hI := Complex.I_sq
  fin_cases k
  · change (Complex.I*R/4 - Complex.I/4 + U/4) = (1) * ((U + Complex.I*(R-1))/4)
    linear_combination 0 * hs
  · change (Complex.I*R*U/8 - Complex.I*U/8 + R/4 + 1/4) = (Complex.I*R/4 - Complex.I/4 + U/4) * ((U + Complex.I*(R-1))/4)
    linear_combination (-R^2/16 + R/8 - 1/16) * hI + (-1/16) * hu + (1/16) * hs
  · change (Complex.I*R/4 + Complex.I/4 + R*U/8 - U/8) = (Complex.I*R*U/8 - Complex.I*U/8 + R/4 + 1/4) * ((U + Complex.I*(R-1))/4)
    linear_combination (-R^2*U/32 + R*U/16 - U/32) * hI + (-Complex.I*R/32 + Complex.I/32) * hu + (-Complex.I/8 + U/32) * hs
  · change (Complex.I*U/4 + R/4 - 1/4) = (Complex.I*R/4 + Complex.I/4 + R*U/8 - U/8) * ((U + Complex.I*(R-1))/4)
    linear_combination (1/16 - R^2/16) * hI + (1/32 - R/32) * hu + (-Complex.I*U/32) * hs
  · change (Complex.I) = (Complex.I*U/4 + R/4 - 1/4) * ((U + Complex.I*(R-1))/4)
    linear_combination (-R*U/16 + U/16) * hI + (-Complex.I/16) * hu + (-Complex.I/16) * hs
  · change (Complex.I*U/4 - R/4 + 1/4) = (Complex.I) * ((U + Complex.I*(R-1))/4)
    linear_combination (1/4 - R/4) * hI
  · change (Complex.I*R/4 + Complex.I/4 - R*U/8 + U/8) = (Complex.I*U/4 - R/4 + 1/4) * ((U + Complex.I*(R-1))/4)
    linear_combination (-R*U/16 + U/16) * hI + (-Complex.I/16) * hu + (Complex.I/16) * hs
  · change (Complex.I*R*U/8 - Complex.I*U/8 - R/4 - 1/4) = (Complex.I*R/4 + Complex.I/4 - R*U/8 + U/8) * ((U + Complex.I*(R-1))/4)
    linear_combination (1/16 - R^2/16) * hI + (R/32 - 1/32) * hu + (Complex.I*U/32 + 1/8) * hs
  · change (Complex.I*R/4 - Complex.I/4 - U/4) = (Complex.I*R*U/8 - Complex.I*U/8 - R/4 - 1/4) * ((U + Complex.I*(R-1))/4)
    linear_combination (-R^2*U/32 + R*U/16 - U/32) * hI + (-Complex.I*R/32 + Complex.I/32) * hu + (U/32) * hs
  · change (-1) = (Complex.I*R/4 - Complex.I/4 - U/4) * ((U + Complex.I*(R-1))/4)
    linear_combination (-R^2/16 + R/8 - 1/16) * hI + (1/16) * hu + (1/16) * hs
  · change (-Complex.I*R/4 + Complex.I/4 - U/4) = (-1) * ((U + Complex.I*(R-1))/4)
    linear_combination 0 * hs
  · change (-Complex.I*R*U/8 + Complex.I*U/8 - R/4 - 1/4) = (-Complex.I*R/4 + Complex.I/4 - U/4) * ((U + Complex.I*(R-1))/4)
    linear_combination (R^2/16 - R/8 + 1/16) * hI + (1/16) * hu + (-1/16) * hs
  · change (-Complex.I*R/4 - Complex.I/4 - R*U/8 + U/8) = (-Complex.I*R*U/8 + Complex.I*U/8 - R/4 - 1/4) * ((U + Complex.I*(R-1))/4)
    linear_combination (R^2*U/32 - R*U/16 + U/32) * hI + (Complex.I*R/32 - Complex.I/32) * hu + (Complex.I/8 - U/32) * hs
  · change (-Complex.I*U/4 - R/4 + 1/4) = (-Complex.I*R/4 - Complex.I/4 - R*U/8 + U/8) * ((U + Complex.I*(R-1))/4)
    linear_combination (R^2/16 - 1/16) * hI + (R/32 - 1/32) * hu + (Complex.I*U/32) * hs
  · change (-Complex.I) = (-Complex.I*U/4 - R/4 + 1/4) * ((U + Complex.I*(R-1))/4)
    linear_combination (R*U/16 - U/16) * hI + (Complex.I/16) * hu + (Complex.I/16) * hs
  · change (-Complex.I*U/4 + R/4 - 1/4) = (-Complex.I) * ((U + Complex.I*(R-1))/4)
    linear_combination (R/4 - 1/4) * hI
  · change (-Complex.I*R/4 - Complex.I/4 + R*U/8 - U/8) = (-Complex.I*U/4 + R/4 - 1/4) * ((U + Complex.I*(R-1))/4)
    linear_combination (R*U/16 - U/16) * hI + (Complex.I/16) * hu + (-Complex.I/16) * hs
  · change (-Complex.I*R*U/8 + Complex.I*U/8 + R/4 + 1/4) = (-Complex.I*R/4 - Complex.I/4 + R*U/8 - U/8) * ((U + Complex.I*(R-1))/4)
    linear_combination (R^2/16 - 1/16) * hI + (1/32 - R/32) * hu + (-Complex.I*U/32 - 1/8) * hs
  · change (-Complex.I*R/4 + Complex.I/4 + U/4) = (-Complex.I*R*U/8 + Complex.I*U/8 + R/4 + 1/4) * ((U + Complex.I*(R-1))/4)
    linear_combination (R^2*U/32 - R*U/16 + U/32) * hI + (Complex.I*R/32 - Complex.I/32) * hu + (-U/32) * hs
  · change (1) = (-Complex.I*R/4 + Complex.I/4 + U/4) * ((U + Complex.I*(R-1))/4)
    linear_combination (R^2/16 - R/8 + 1/16) * hI + (-1/16) * hu + (-1/16) * hs

def phase (n : ℕ) : ℂ := phaseTable (s : ℂ) (u : ℂ) ⟨n % 20, Nat.mod_lt _ (by omega)⟩

lemma phase_succ (n : ℕ) : phase (n+1) = phase n * zeta := by
  have hs : (s : ℂ)^2 = 5 := by exact_mod_cast s_sq
  have hu : (u : ℂ)^2 = 10 + 2*(s : ℂ) := by exact_mod_cast u_sq
  have h := phaseTable_step (s : ℂ) (u : ℂ) hs hu ⟨n%20, Nat.mod_lt _ (by omega)⟩
  simpa [phase, zeta, Nat.add_mod] using h

lemma phase_eq_pow (n : ℕ) : phase n = zeta^n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [phase_succ, ih, pow_succ]

lemma zeta_pow_twenty : zeta^20 = 1 := by
  rw [← phase_eq_pow]
  norm_num [phase, phaseTable]

lemma phase_mod (n : ℕ) : phase (n%20) = phase n := by
  simp [phase]

lemma phase_add (n m : ℕ) : phase (n+m) = phase n * phase m := by
  simp only [phase_eq_pow, pow_add]

lemma phase_zero : phase 0 = 1 := by rfl
lemma phase_five : phase 5 = Complex.I := by norm_num [phase, phaseTable]


lemma star_phaseTable (k : Fin 20) : star (phaseTable (s : ℂ) (u : ℂ) k) =
    phaseTable (s : ℂ) (u : ℂ) ⟨(20-k.val)%20, Nat.mod_lt _ (by omega)⟩ := by
  fin_cases k <;> simp [phaseTable] <;> ring

lemma star_phase (n : ℕ) : star (phase n) = phase (20 - n%20) := by
  exact star_phaseTable ⟨n%20, Nat.mod_lt _ (by omega)⟩

lemma phase_mul_star (n : ℕ) : phase n * star (phase n) = 1 := by
  rw [star_phase, ← phase_add]
  have he : (n + (20-n%20))%20 = 0 := by omega
  rw [← phase_mod, he, phase_zero]

lemma phase_norm (n : ℕ) : ‖phase n‖ = 1 := by
  have h := phase_mul_star n
  have hn := congrArg norm h
  simp only [norm_mul, norm_star, norm_one] at hn
  nlinarith [norm_nonneg (phase n)]

end
end CGLMP5.Attainment
