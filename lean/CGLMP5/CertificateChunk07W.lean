import CGLMP5.CertificateChunkData07

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk07W_decode : chunkScalar07W.decode = some (term07.weight) := by decide +kernel

end CGLMP5.CertificateSource
