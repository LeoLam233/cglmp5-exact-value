import CGLMP5.AttainmentState
import CGLMP5.CanonicalData
import CGLMP5.ScalarEncoding

namespace CGLMP5.Attainment
noncomputable section

/-- The five exact serialized Schmidt coordinates evaluate to the physical state coefficients. -/
theorem canonical_gamma :
    CanonicalData.gamma.map Scalar.eval = (List.ofFn gamma).map (fun a : ℝ => (a : ℂ)) := by
  norm_num [CanonicalData.gamma, CanonicalData.decodeScalar, CertificateSource.gammaRaw,
    Scalar.ofCanonical, Scalar.eval, Scalar.basisEval, Fin.sum_univ_succ, gamma,
    schmidtA, schmidtB, coeffA, coeffB, x, List.ofFn_succ]
  <;> push_cast <;> ring_nf <;> simp

end
end CGLMP5.Attainment
