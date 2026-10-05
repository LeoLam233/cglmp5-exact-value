import CGLMP5.AttainmentSource
import CGLMP5.CertificateHeaderProofs

namespace CGLMP5.Attainment
noncomputable section
open CertificateSource

/-- The uninterrupted decimal strings rendered in the canonical header decode and evaluate
exactly to the five physical Schmidt amplitudes used by the attaining strategy. -/
theorem canonical_header_gamma_evaluation :
    ((sourceHeaderGamma.map ChunkScalar.toText).mapM TextScalar.decode).map
      (fun rs => (rs.map CanonicalData.decodeScalar).map Scalar.eval) =
    some ((List.ofFn gamma).map (fun a : ℝ => (a : ℂ))) := by
  rw [header_gamma_text_decode, Option.map_some]
  change some (CanonicalData.gamma.map Scalar.eval) = _
  rw [canonical_gamma]

end
end CGLMP5.Attainment
