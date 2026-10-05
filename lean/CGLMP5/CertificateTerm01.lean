import CGLMP5.CertificateChunk01W
import CGLMP5.CertificateChunk01C00
import CGLMP5.CertificateChunk01C01
import CGLMP5.CertificateChunk01C02
import CGLMP5.CertificateChunk01C03
import CGLMP5.CertificateChunk01C04
import CGLMP5.CertificateChunk01C05
import CGLMP5.CertificateChunk01C06
import CGLMP5.CertificateChunk01C07
import CGLMP5.CertificateChunk01C08
import CGLMP5.CertificateChunk01C09
import CGLMP5.CertificateChunk01C10
import CGLMP5.CertificateChunk01C11

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem term01_source_decode : chunkTerm01.decode = some term01 := by
  simp only [ChunkTerm.decode, chunkTerm01, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]
  simp only [chunk01W_decode, chunk01C00_decode, chunk01C01_decode, chunk01C02_decode, chunk01C03_decode, chunk01C04_decode, chunk01C05_decode, chunk01C06_decode, chunk01C07_decode, chunk01C08_decode, chunk01C09_decode, chunk01C10_decode, chunk01C11_decode, Option.bind_some, Option.map_some]
  rfl

end CGLMP5.CertificateSource
