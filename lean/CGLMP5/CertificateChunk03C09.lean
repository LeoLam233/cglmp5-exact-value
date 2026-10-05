import CGLMP5.CertificateChunkData03

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk03C09_decode : chunkScalar03C09.decode = some ((term03.polynomial[9]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
