import CGLMP5.CertificateChunkData13

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk13C06_decode : chunkScalar13C06.decode = some ((term13.polynomial[6]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
