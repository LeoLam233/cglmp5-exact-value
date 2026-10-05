import CGLMP5.CertificateChunk13W
import CGLMP5.CertificateChunk13C00
import CGLMP5.CertificateChunk13C01
import CGLMP5.CertificateChunk13C02
import CGLMP5.CertificateChunk13C03
import CGLMP5.CertificateChunk13C04
import CGLMP5.CertificateChunk13C05
import CGLMP5.CertificateChunk13C06
import CGLMP5.CertificateChunk13C07
import CGLMP5.CertificateChunk13C08
import CGLMP5.CertificateChunk13C09
import CGLMP5.CertificateChunk13C10
import CGLMP5.CertificateChunk13C11

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem term13_source_decode : chunkTerm13.decode = some term13 := by
  simp only [ChunkTerm.decode, chunkTerm13, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]
  simp only [chunk13W_decode, chunk13C00_decode, chunk13C01_decode, chunk13C02_decode, chunk13C03_decode, chunk13C04_decode, chunk13C05_decode, chunk13C06_decode, chunk13C07_decode, chunk13C08_decode, chunk13C09_decode, chunk13C10_decode, chunk13C11_decode, Option.bind_some, Option.map_some]
  rfl

end CGLMP5.CertificateSource
