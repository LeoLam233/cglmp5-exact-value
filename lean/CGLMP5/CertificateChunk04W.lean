import CGLMP5.CertificateChunkData04

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk04W_decode : chunkScalar04W.decode = some (term04.weight) := by decide +kernel

end CGLMP5.CertificateSource
