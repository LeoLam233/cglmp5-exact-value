import CGLMP5.CertificateChunkData06

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem chunk06C14_decode : chunkScalar06C14.decode = some ((term06.polynomial[14]'(by decide)).coefficient) := by decide +kernel

end CGLMP5.CertificateSource
