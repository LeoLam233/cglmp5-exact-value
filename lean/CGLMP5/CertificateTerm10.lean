import CGLMP5.CertificateChunk10W
import CGLMP5.CertificateChunk10C00
import CGLMP5.CertificateChunk10C01
import CGLMP5.CertificateChunk10C02
import CGLMP5.CertificateChunk10C03
import CGLMP5.CertificateChunk10C04
import CGLMP5.CertificateChunk10C05
import CGLMP5.CertificateChunk10C06
import CGLMP5.CertificateChunk10C07
import CGLMP5.CertificateChunk10C08
import CGLMP5.CertificateChunk10C09
import CGLMP5.CertificateChunk10C10
import CGLMP5.CertificateChunk10C11

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem term10_source_decode : chunkTerm10.decode = some term10 := by
  simp only [ChunkTerm.decode, chunkTerm10, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]
  simp only [chunk10W_decode, chunk10C00_decode, chunk10C01_decode, chunk10C02_decode, chunk10C03_decode, chunk10C04_decode, chunk10C05_decode, chunk10C06_decode, chunk10C07_decode, chunk10C08_decode, chunk10C09_decode, chunk10C10_decode, chunk10C11_decode, Option.bind_some, Option.map_some]
  rfl

end CGLMP5.CertificateSource
