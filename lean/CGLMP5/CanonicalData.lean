import Init.Data.Rat.Lemmas
import CGLMP5.CertificateData
import CGLMP5.ScalarSyntax

/-! Exact computational scalar data, directly decoded from the source-bound typed records. -/
namespace CGLMP5.CanonicalData
open CertificateSource

/-- Missing coordinates are syntactically assigned zero, while `valid` proves none are missing. -/
def decodeScalar (s : RawScalar) : Scalar :=
  Scalar.ofCanonical (fun k => (s.numerators[k.val]?).getD 0) s.denominator

def rawTerm (j : Fin 14) : RawTerm :=
  rawTerms[j.val]'(by rw [rawTerms_length]; exact j.isLt)

def weight (j : Fin 14) : Scalar := decodeScalar (rawTerm j).weight

def polynomial (j : Fin 14) : List (Word × Scalar) :=
  (rawTerm j).polynomial.map fun c => (c.toWord, decodeScalar c.coefficient)

theorem rawTerm_valid (j : Fin 14) : (rawTerm j).valid := by
  apply rawTerms_valid
  exact List.getElem_mem _

theorem weight_denominator_pos (j : Fin 14) : 0 < (rawTerm j).weight.denominator :=
  (rawTerm_valid j).1.2

theorem weight_coordinates_length (j : Fin 14) : (rawTerm j).weight.numerators.length = 24 :=
  (rawTerm_valid j).1.1

/-- Every compact weight has exactly zero imaginary-half coordinates. -/
theorem weight_isReal (j : Fin 14) : Scalar.isReal (weight j) := by
  have hz : ∀ (l : Fin 14) (k : Fin 24), 12 ≤ k.val →
      ((rawTerm l).weight.numerators[k.val]?).getD 0 = 0 := by decide
  intro k hk
  simp [weight, decodeScalar, Scalar.ofCanonical, hz j k hk, Rat.div_def, Rat.zero_mul]

def decodeRational (q : RawRational) : ℚ := (q.numerator : ℚ) / q.denominator

def muLower : ℚ := decodeRational muBox.lower
def muUpper : ℚ := decodeRational muBox.upper
def sLower : ℚ := decodeRational sBox.lower
def sUpper : ℚ := decodeRational sBox.upper
def uLower : ℚ := decodeRational uBox.lower
def uUpper : ℚ := decodeRational uBox.upper

def gamma : List Scalar := gammaRaw.map decodeScalar

end CGLMP5.CanonicalData
