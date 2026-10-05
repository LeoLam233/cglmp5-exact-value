import CGLMP5.CertificateChunkData13

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk13C02_decode : chunkScalar13C02.decode = some ((term13.polynomial[2]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
