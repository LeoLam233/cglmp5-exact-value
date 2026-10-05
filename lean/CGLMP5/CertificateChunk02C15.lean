import CGLMP5.CertificateChunkData02

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk02C15_decode : chunkScalar02C15.decode = some ((term02.polynomial[15]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
