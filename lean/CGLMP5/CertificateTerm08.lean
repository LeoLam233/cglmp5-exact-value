import CGLMP5.CertificateChunk08W
import CGLMP5.CertificateChunk08C00
import CGLMP5.CertificateChunk08C01
import CGLMP5.CertificateChunk08C02
import CGLMP5.CertificateChunk08C03
import CGLMP5.CertificateChunk08C04
import CGLMP5.CertificateChunk08C05
import CGLMP5.CertificateChunk08C06
import CGLMP5.CertificateChunk08C07

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem term08_source_decode : chunkTerm08.decode = some term08 := by
  simp only [ChunkTerm.decode, chunkTerm08, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]
  simp only [chunk08W_decode, chunk08C00_decode, chunk08C01_decode, chunk08C02_decode, chunk08C03_decode, chunk08C04_decode, chunk08C05_decode, chunk08C06_decode, chunk08C07_decode, Option.bind_some, Option.map_some]
  rfl

end CGLMP5.CertificateSource
