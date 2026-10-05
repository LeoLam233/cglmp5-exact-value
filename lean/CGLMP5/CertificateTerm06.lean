import CGLMP5.CertificateChunk06W
import CGLMP5.CertificateChunk06C00
import CGLMP5.CertificateChunk06C01
import CGLMP5.CertificateChunk06C02
import CGLMP5.CertificateChunk06C03
import CGLMP5.CertificateChunk06C04
import CGLMP5.CertificateChunk06C05
import CGLMP5.CertificateChunk06C06
import CGLMP5.CertificateChunk06C07
import CGLMP5.CertificateChunk06C08
import CGLMP5.CertificateChunk06C09
import CGLMP5.CertificateChunk06C10
import CGLMP5.CertificateChunk06C11
import CGLMP5.CertificateChunk06C12
import CGLMP5.CertificateChunk06C13
import CGLMP5.CertificateChunk06C14
import CGLMP5.CertificateChunk06C15

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem term06_source_decode : chunkTerm06.decode = some term06 := by
  simp only [ChunkTerm.decode, chunkTerm06, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]
  simp only [chunk06W_decode, chunk06C00_decode, chunk06C01_decode, chunk06C02_decode, chunk06C03_decode, chunk06C04_decode, chunk06C05_decode, chunk06C06_decode, chunk06C07_decode, chunk06C08_decode, chunk06C09_decode, chunk06C10_decode, chunk06C11_decode, chunk06C12_decode, chunk06C13_decode, chunk06C14_decode, chunk06C15_decode, Option.bind_some, Option.map_some]
  rfl

end CGLMP5.CertificateSource
