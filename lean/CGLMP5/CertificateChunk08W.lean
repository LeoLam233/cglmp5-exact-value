import CGLMP5.CertificateChunkData08

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk08W_decode : chunkScalar08W.decode = some (term08.weight) := by decide +kernel

end CGLMP5.CertificateSource
