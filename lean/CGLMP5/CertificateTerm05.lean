import CGLMP5.CertificateChunk05W
import CGLMP5.CertificateChunk05C00
import CGLMP5.CertificateChunk05C01
import CGLMP5.CertificateChunk05C02
import CGLMP5.CertificateChunk05C03

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem term05_source_decode : chunkTerm05.decode = some term05 := by
  simp only [ChunkTerm.decode, chunkTerm05, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]
  simp only [chunk05W_decode, chunk05C00_decode, chunk05C01_decode, chunk05C02_decode, chunk05C03_decode, Option.bind_some, Option.map_some]
  rfl

end CGLMP5.CertificateSource
