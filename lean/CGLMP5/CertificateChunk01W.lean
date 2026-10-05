import CGLMP5.CertificateChunkData01

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk01W_decode : chunkScalar01W.decode = some (term01.weight) := by decide +kernel

end CGLMP5.CertificateSource
