import CGLMP5.CertificateChunk07W
import CGLMP5.CertificateChunk07C00
import CGLMP5.CertificateChunk07C01
import CGLMP5.CertificateChunk07C02
import CGLMP5.CertificateChunk07C03
import CGLMP5.CertificateChunk07C04
import CGLMP5.CertificateChunk07C05
import CGLMP5.CertificateChunk07C06
import CGLMP5.CertificateChunk07C07
import CGLMP5.CertificateChunk07C08
import CGLMP5.CertificateChunk07C09
import CGLMP5.CertificateChunk07C10
import CGLMP5.CertificateChunk07C11

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem term07_source_decode : chunkTerm07.decode = some term07 := by
  simp only [ChunkTerm.decode, chunkTerm07, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]
  simp only [chunk07W_decode, chunk07C00_decode, chunk07C01_decode, chunk07C02_decode, chunk07C03_decode, chunk07C04_decode, chunk07C05_decode, chunk07C06_decode, chunk07C07_decode, chunk07C08_decode, chunk07C09_decode, chunk07C10_decode, chunk07C11_decode, Option.bind_some, Option.map_some]
  rfl

end CGLMP5.CertificateSource
