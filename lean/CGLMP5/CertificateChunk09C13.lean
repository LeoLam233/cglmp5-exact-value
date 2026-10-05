import CGLMP5.CertificateChunkData09

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk09C13_decode : chunkScalar09C13.decode = some ((term09.polynomial[13]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
