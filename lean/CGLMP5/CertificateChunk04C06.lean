import CGLMP5.CertificateChunkData04

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk04C06_decode : chunkScalar04C06.decode = some ((term04.polynomial[6]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
