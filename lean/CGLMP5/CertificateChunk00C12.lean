import CGLMP5.CertificateChunkData00

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk00C12_decode : chunkScalar00C12.decode = some ((term00.polynomial[12]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
