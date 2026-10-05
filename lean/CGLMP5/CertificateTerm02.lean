import CGLMP5.CertificateChunk02W
import CGLMP5.CertificateChunk02C00
import CGLMP5.CertificateChunk02C01
import CGLMP5.CertificateChunk02C02
import CGLMP5.CertificateChunk02C03
import CGLMP5.CertificateChunk02C04
import CGLMP5.CertificateChunk02C05
import CGLMP5.CertificateChunk02C06
import CGLMP5.CertificateChunk02C07
import CGLMP5.CertificateChunk02C08
import CGLMP5.CertificateChunk02C09
import CGLMP5.CertificateChunk02C10
import CGLMP5.CertificateChunk02C11
import CGLMP5.CertificateChunk02C12
import CGLMP5.CertificateChunk02C13
import CGLMP5.CertificateChunk02C14
import CGLMP5.CertificateChunk02C15

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem term02_source_decode : chunkTerm02.decode = some term02 := by
  simp only [ChunkTerm.decode, chunkTerm02, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]
  simp only [chunk02W_decode, chunk02C00_decode, chunk02C01_decode, chunk02C02_decode, chunk02C03_decode, chunk02C04_decode, chunk02C05_decode, chunk02C06_decode, chunk02C07_decode, chunk02C08_decode, chunk02C09_decode, chunk02C10_decode, chunk02C11_decode, chunk02C12_decode, chunk02C13_decode, chunk02C14_decode, chunk02C15_decode, Option.bind_some, Option.map_some]
  rfl

end CGLMP5.CertificateSource
