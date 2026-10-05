import CGLMP5.CertificateChunkData05

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk05C02_decode : chunkScalar05C02.decode = some ((term05.polynomial[2]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
