import CGLMP5.CertificateChunkData05

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk05C03_decode : chunkScalar05C03.decode = some ((term05.polynomial[3]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
