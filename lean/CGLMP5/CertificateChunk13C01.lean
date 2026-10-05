import CGLMP5.CertificateChunkData13

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk13C01_decode : chunkScalar13C01.decode = some ((term13.polynomial[1]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
