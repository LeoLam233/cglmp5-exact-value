import CGLMP5.CertificateChunk11W
import CGLMP5.CertificateChunk11C00
import CGLMP5.CertificateChunk11C01
import CGLMP5.CertificateChunk11C02
import CGLMP5.CertificateChunk11C03

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem term11_source_decode : chunkTerm11.decode = some term11 := by
  simp only [ChunkTerm.decode, chunkTerm11, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]
  simp only [chunk11W_decode, chunk11C00_decode, chunk11C01_decode, chunk11C02_decode, chunk11C03_decode, Option.bind_some, Option.map_some]
  rfl

end CGLMP5.CertificateSource
