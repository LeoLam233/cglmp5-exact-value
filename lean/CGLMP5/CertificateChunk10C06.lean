import CGLMP5.CertificateChunkData10

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk10C06_decode : chunkScalar10C06.decode = some ((term10.polynomial[6]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
