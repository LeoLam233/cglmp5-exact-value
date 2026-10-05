import CGLMP5.CertificateChunkData10

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk10C02_decode : chunkScalar10C02.decode = some ((term10.polynomial[2]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
