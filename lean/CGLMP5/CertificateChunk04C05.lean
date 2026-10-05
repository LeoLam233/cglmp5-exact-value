import CGLMP5.CertificateChunkData04

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk04C05_decode : chunkScalar04C05.decode = some ((term04.polynomial[5]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
