import CGLMP5.CertificateChunkData11

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk11C01_decode : chunkScalar11C01.decode = some ((term11.polynomial[1]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
