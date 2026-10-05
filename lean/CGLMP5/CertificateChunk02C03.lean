import CGLMP5.CertificateChunkData02

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk02C03_decode : chunkScalar02C03.decode = some ((term02.polynomial[3]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
