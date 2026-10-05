import CGLMP5.CertificateChunkData11

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk11W_decode : chunkScalar11W.decode = some (term11.weight) := by decide +kernel

end CGLMP5.CertificateSource
