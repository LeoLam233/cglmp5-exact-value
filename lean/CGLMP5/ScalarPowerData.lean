import CGLMP5.ScalarTableData
import Mathlib.Data.Fin.VecNotation

namespace CGLMP5.Scalar

/-- Exact scalar coordinates of the selected twentieth root. -/
def zetaExact : Scalar := ofCanonical
  ![0,0,0,0,0,0,1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0] 4

/-- Exact scalar coordinates of the selected Bell value. -/
def muExact : Scalar := ofCanonical
  ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] 5

def pow (a : Scalar) : ℕ → Scalar
  | 0 => ofRat 1
  | n+1 => mul (pow a n) a

end CGLMP5.Scalar
