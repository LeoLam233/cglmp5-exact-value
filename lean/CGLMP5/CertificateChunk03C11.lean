import CGLMP5.CertificateChunkData03

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk03C11_decode : chunkScalar03C11.decode = some ((term03.polynomial[11]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
