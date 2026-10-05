import CGLMP5.CertificateChunkData03

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk03W_decode : chunkScalar03W.decode = some (term03.weight) := by decide +kernel

end CGLMP5.CertificateSource
