import CGLMP5.CertificateChunk00W
import CGLMP5.CertificateChunk00C00
import CGLMP5.CertificateChunk00C01
import CGLMP5.CertificateChunk00C02
import CGLMP5.CertificateChunk00C03
import CGLMP5.CertificateChunk00C04
import CGLMP5.CertificateChunk00C05
import CGLMP5.CertificateChunk00C06
import CGLMP5.CertificateChunk00C07
import CGLMP5.CertificateChunk00C08
import CGLMP5.CertificateChunk00C09
import CGLMP5.CertificateChunk00C10
import CGLMP5.CertificateChunk00C11
import CGLMP5.CertificateChunk00C12
import CGLMP5.CertificateChunk00C13
import CGLMP5.CertificateChunk00C14
import CGLMP5.CertificateChunk00C15

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem term00_source_decode : chunkTerm00.decode = some term00 := by
  simp only [ChunkTerm.decode, chunkTerm00, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]
  simp only [chunk00W_decode, chunk00C00_decode, chunk00C01_decode, chunk00C02_decode, chunk00C03_decode, chunk00C04_decode, chunk00C05_decode, chunk00C06_decode, chunk00C07_decode, chunk00C08_decode, chunk00C09_decode, chunk00C10_decode, chunk00C11_decode, chunk00C12_decode, chunk00C13_decode, chunk00C14_decode, chunk00C15_decode, Option.bind_some, Option.map_some]
  rfl

end CGLMP5.CertificateSource
