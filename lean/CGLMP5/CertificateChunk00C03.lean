import CGLMP5.CertificateChunkData00

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk00C03_decode : chunkScalar00C03.decode = some ((term00.polynomial[3]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
