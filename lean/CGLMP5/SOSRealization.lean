import CGLMP5.ScalarDefs
import CGLMP5.CanonicalData
import CGLMP5.SOSPolynomial

namespace CGLMP5.SOS
noncomputable section

/-- The fourteen canonical compact polynomials evaluated in an arbitrary representation. -/
def realizingPolynomial {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
    (a b : Fin 2 → unitary R) (j : Fin 14) : R :=
  evaluate a b ((CanonicalData.polynomial j).map fun t => (t.1, Scalar.eval t.2))

end
end CGLMP5.SOS
