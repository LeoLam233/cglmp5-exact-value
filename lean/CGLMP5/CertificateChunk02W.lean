import CGLMP5.CertificateChunkData02

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk02W_decode : chunkScalar02W.decode = some (term02.weight) := by decide +kernel

end CGLMP5.CertificateSource
