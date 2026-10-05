import CGLMP5.CertificateChunkData00

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk00W_decode : chunkScalar00W.decode = some (term00.weight) := by decide +kernel

end CGLMP5.CertificateSource
