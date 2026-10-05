import CGLMP5.ScalarTableData

/-! Pure executable integer convolution; no tactic or analytic imports. -/
namespace CGLMP5.Scalar

/-- Integer numerator of the existing sparse scalar multiplication table. -/
def mulNumerator (n m : Fin 24 → ℤ) (k : Fin 24) : ℤ :=
  ((mulTerms k).map fun t => n t.1 * m t.2.1 * t.2.2).sum

end CGLMP5.Scalar
