import CGLMP5.ScalarDefs
import CGLMP5.SOSFeatureData
import CGLMP5.SOSPolynomial

/-! Exact finite scalar reflection into arbitrary allowed representations. -/
namespace CGLMP5.SOSFinite

@[simp] theorem sumScalars_nil : sumScalars [] = Scalar.zero := rfl
@[simp] theorem sumScalars_cons (s : Scalar) (ss : List Scalar) :
    sumScalars (s :: ss) = Scalar.add s (sumScalars ss) := rfl

theorem eval_sumScalars (ss : List Scalar) :
    Scalar.eval (sumScalars ss) = (ss.map Scalar.eval).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih => simp [ih]

noncomputable def complexPolynomial (p : List (Word × Scalar)) : SOS.Polynomial :=
  p.map fun t => (t.1, Scalar.eval t.2)

def scalarCoefficient (p : List (Word × Scalar)) (w : Word) : Scalar :=
  sumScalars (((p.filter fun t => t.1 = w).map Prod.snd))

@[simp] theorem scalarCoefficient_cons (t : Word × Scalar) (p : List (Word × Scalar))
    (w : Word) : scalarCoefficient (t :: p) w =
      if t.1 = w then Scalar.add t.2 (scalarCoefficient p w) else scalarCoefficient p w := by
  by_cases h : t.1 = w <;> simp [scalarCoefficient, h]

theorem coefficient_complexPolynomial (p : List (Word × Scalar)) (w : Word) :
    SOS.coefficient (complexPolynomial p) w = Scalar.eval (scalarCoefficient p w) := by
  induction p with
  | nil => simp [complexPolynomial, scalarCoefficient]
  | cons t p ih =>
    simp only [complexPolynomial, List.map_cons, SOS.coefficient_cons]
    change (if t.1 = w then Scalar.eval t.2 else 0) +
      SOS.coefficient (complexPolynomial p) w = Scalar.eval (scalarCoefficient (t :: p) w)
    rw [scalarCoefficient_cons]
    by_cases h : t.1 = w <;> simp [h, ih]

noncomputable section
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  (a b : Fin 2 → unitary R)

/-- Collecting by a finite index needs no assumption that the represented words differ. -/
theorem evaluate_indexed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (word : ι → Word) (es : List (ι × Scalar)) :
    SOS.evaluate a b (es.map fun t => (word t.1, Scalar.eval t.2)) =
      ∑ i : ι, Scalar.eval (sumScalars (((es.filter fun t => t.1 = i).map Prod.snd))) •
        Word.evalStar a b (word i) := by
  induction es with
  | nil => simp
  | cons t es ih =>
    simp only [List.map_cons, SOS.evaluate_cons]
    rw [ih]
    have hcoeff (i : ι) :
        Scalar.eval (sumScalars ((((t :: es).filter fun u => u.1 = i).map Prod.snd))) =
          (if t.1 = i then Scalar.eval t.2 else 0) +
            Scalar.eval (sumScalars (((es.filter fun u => u.1 = i).map Prod.snd))) := by
      by_cases h : t.1 = i <;> simp [h]
    simp only [hcoeff, add_smul, Finset.sum_add_distrib]
    congr 1
    simp [eq_comm]

/-- A finite vector of exact scalar coefficient equalities suffices for operator equality. -/
theorem evaluate_indexed_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (word : ι → Word) (es fs : List (ι × Scalar))
    (hcoeff : ∀ i,
      sumScalars (((es.filter fun t => t.1 = i).map Prod.snd)) =
      sumScalars (((fs.filter fun t => t.1 = i).map Prod.snd))) :
    SOS.evaluate a b (es.map fun t => (word t.1, Scalar.eval t.2)) =
      SOS.evaluate a b (fs.map fun t => (word t.1, Scalar.eval t.2)) := by
  rw [evaluate_indexed a b, evaluate_indexed a b]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcoeff i]

end
end CGLMP5.SOSFinite
