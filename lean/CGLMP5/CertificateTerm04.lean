import CGLMP5.CertificateChunk04W
import CGLMP5.CertificateChunk04C00
import CGLMP5.CertificateChunk04C01
import CGLMP5.CertificateChunk04C02
import CGLMP5.CertificateChunk04C03
import CGLMP5.CertificateChunk04C04
import CGLMP5.CertificateChunk04C05
import CGLMP5.CertificateChunk04C06
import CGLMP5.CertificateChunk04C07

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem term04_source_decode : chunkTerm04.decode = some term04 := by
  simp only [ChunkTerm.decode, chunkTerm04, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]
  simp only [chunk04W_decode, chunk04C00_decode, chunk04C01_decode, chunk04C02_decode, chunk04C03_decode, chunk04C04_decode, chunk04C05_decode, chunk04C06_decode, chunk04C07_decode, Option.bind_some, Option.map_some]
  rfl

end CGLMP5.CertificateSource
