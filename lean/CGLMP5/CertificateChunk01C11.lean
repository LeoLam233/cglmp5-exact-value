import CGLMP5.CertificateChunkData01

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk01C11_decode : chunkScalar01C11.decode = some ((term01.polynomial[11]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
