import CGLMP5.CertificateChunkData10

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk10W_decode : chunkScalar10W.decode = some (term10.weight) := by decide +kernel

end CGLMP5.CertificateSource
