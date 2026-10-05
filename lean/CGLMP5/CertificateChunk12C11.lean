import CGLMP5.CertificateChunkData12

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk12C11_decode : chunkScalar12C11.decode = some ((term12.polynomial[11]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
