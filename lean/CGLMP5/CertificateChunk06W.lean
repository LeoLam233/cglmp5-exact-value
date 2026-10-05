import CGLMP5.CertificateChunkData06

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk06W_decode : chunkScalar06W.decode = some (term06.weight) := by decide +kernel

end CGLMP5.CertificateSource
