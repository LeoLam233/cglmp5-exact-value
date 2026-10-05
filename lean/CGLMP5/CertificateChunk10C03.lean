import CGLMP5.CertificateChunkData10

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk10C03_decode : chunkScalar10C03.decode = some ((term10.polynomial[3]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
