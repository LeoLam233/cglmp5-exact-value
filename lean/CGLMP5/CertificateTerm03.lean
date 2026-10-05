import CGLMP5.CertificateChunk03W
import CGLMP5.CertificateChunk03C00
import CGLMP5.CertificateChunk03C01
import CGLMP5.CertificateChunk03C02
import CGLMP5.CertificateChunk03C03
import CGLMP5.CertificateChunk03C04
import CGLMP5.CertificateChunk03C05
import CGLMP5.CertificateChunk03C06
import CGLMP5.CertificateChunk03C07
import CGLMP5.CertificateChunk03C08
import CGLMP5.CertificateChunk03C09
import CGLMP5.CertificateChunk03C10
import CGLMP5.CertificateChunk03C11

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem term03_source_decode : chunkTerm03.decode = some term03 := by
  simp only [ChunkTerm.decode, chunkTerm03, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]
  simp only [chunk03W_decode, chunk03C00_decode, chunk03C01_decode, chunk03C02_decode, chunk03C03_decode, chunk03C04_decode, chunk03C05_decode, chunk03C06_decode, chunk03C07_decode, chunk03C08_decode, chunk03C09_decode, chunk03C10_decode, chunk03C11_decode, Option.bind_some, Option.map_some]
  rfl

end CGLMP5.CertificateSource
