import CGLMP5.CertificateChunkData01

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk01C06_decode : chunkScalar01C06.decode = some ((term01.polynomial[6]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
