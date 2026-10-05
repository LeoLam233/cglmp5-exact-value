import CGLMP5.CertificateChunkData12

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk12W_decode : chunkScalar12W.decode = some (term12.weight) := by decide +kernel

end CGLMP5.CertificateSource
