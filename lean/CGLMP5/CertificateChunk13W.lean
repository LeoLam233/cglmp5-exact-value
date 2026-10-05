import CGLMP5.CertificateChunkData13

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk13W_decode : chunkScalar13W.decode = some (term13.weight) := by decide +kernel

end CGLMP5.CertificateSource
