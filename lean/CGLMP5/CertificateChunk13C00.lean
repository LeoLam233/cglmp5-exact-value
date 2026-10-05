import CGLMP5.CertificateChunkData13

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk13C00_decode : chunkScalar13C00.decode = some ((term13.polynomial[0]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
