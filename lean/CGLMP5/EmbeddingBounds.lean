import CGLMP5.ScalarIntervals

/-!
# Small proof-only rational boxes for the actual embedding

The frozen artifact explicitly permits broader valid boxes. These twelve-digit
boxes are proved directly below and suffice for all fourteen weights. They are
not assumptions imported from floating-point computations or historical flags.
-/

namespace CGLMP5.ProofBounds

def muI : QInterval := ⟨3015710475522/1000000000000, 3015710475523/1000000000000⟩
def sI : QInterval := ⟨2236067977499/1000000000000, 2236067977500/1000000000000⟩
def uI : QInterval := ⟨3804226065180/1000000000000, 3804226065181/1000000000000⟩
def xI : QInterval := QInterval.scale 5 muI

lemma mu_contains : muI.Contains mu := by
  apply mu_mem_of_signs <;> norm_num [muI, sextic]

lemma s_contains : sI.Contains s := by
  have hl : (sI.lo:ℝ)^2 < 5 := by norm_num [sI]
  have hu : 5 < (sI.hi:ℝ)^2 := by norm_num [sI]
  have hl0 : (0:ℝ) < sI.lo := by norm_num [sI]
  have hu0 : (0:ℝ) < sI.hi := by norm_num [sI]
  constructor <;> nlinarith [s_sq, s_pos]

lemma u_contains : uI.Contains u := by
  have hl : (uI.lo:ℝ)^2 < 10+2*(sI.lo:ℝ) := by norm_num [uI, sI]
  have hu : 10+2*(sI.hi:ℝ) < (uI.hi:ℝ)^2 := by norm_num [uI, sI]
  have hl0 : (0:ℝ) < uI.lo := by norm_num [uI]
  have hu0 : (0:ℝ) < uI.hi := by norm_num [uI]
  constructor <;> nlinarith [u_sq, u_pos, s_contains.1, s_contains.2]

lemma x_contains : xI.Contains x := by
  simpa [x, xI] using QInterval.contains_scale 5 mu_contains

lemma s_lo_nonneg : 0 ≤ sI.lo := by norm_num [sI]
lemma x_lo_nonneg : 0 ≤ xI.lo := by norm_num [xI, muI, QInterval.scale]
lemma u_lo_nonneg : 0 ≤ uI.lo := by norm_num [uI]

lemma scalar_enclosure (a : Scalar) :
    (Scalar.enclosure sI xI uI a).Contains (Scalar.evalReal a) :=
  Scalar.enclosure_contains s_contains x_contains u_contains
    s_lo_nonneg x_lo_nonneg u_lo_nonneg a

end CGLMP5.ProofBounds
