import CGLMP5.CertificateChunk12W
import CGLMP5.CertificateChunk12C00
import CGLMP5.CertificateChunk12C01
import CGLMP5.CertificateChunk12C02
import CGLMP5.CertificateChunk12C03
import CGLMP5.CertificateChunk12C04
import CGLMP5.CertificateChunk12C05
import CGLMP5.CertificateChunk12C06
import CGLMP5.CertificateChunk12C07
import CGLMP5.CertificateChunk12C08
import CGLMP5.CertificateChunk12C09
import CGLMP5.CertificateChunk12C10
import CGLMP5.CertificateChunk12C11
import CGLMP5.CertificateChunk12C12
import CGLMP5.CertificateChunk12C13
import CGLMP5.CertificateChunk12C14
import CGLMP5.CertificateChunk12C15

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem term12_source_decode : chunkTerm12.decode = some term12 := by
  simp only [ChunkTerm.decode, chunkTerm12, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]
  simp only [chunk12W_decode, chunk12C00_decode, chunk12C01_decode, chunk12C02_decode, chunk12C03_decode, chunk12C04_decode, chunk12C05_decode, chunk12C06_decode, chunk12C07_decode, chunk12C08_decode, chunk12C09_decode, chunk12C10_decode, chunk12C11_decode, chunk12C12_decode, chunk12C13_decode, chunk12C14_decode, chunk12C15_decode, Option.bind_some, Option.map_some]
  rfl

end CGLMP5.CertificateSource
