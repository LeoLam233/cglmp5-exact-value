import CGLMP5.CertificateChunk09W
import CGLMP5.CertificateChunk09C00
import CGLMP5.CertificateChunk09C01
import CGLMP5.CertificateChunk09C02
import CGLMP5.CertificateChunk09C03
import CGLMP5.CertificateChunk09C04
import CGLMP5.CertificateChunk09C05
import CGLMP5.CertificateChunk09C06
import CGLMP5.CertificateChunk09C07
import CGLMP5.CertificateChunk09C08
import CGLMP5.CertificateChunk09C09
import CGLMP5.CertificateChunk09C10
import CGLMP5.CertificateChunk09C11
import CGLMP5.CertificateChunk09C12
import CGLMP5.CertificateChunk09C13
import CGLMP5.CertificateChunk09C14
import CGLMP5.CertificateChunk09C15

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem term09_source_decode : chunkTerm09.decode = some term09 := by
  simp only [ChunkTerm.decode, chunkTerm09, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]
  simp only [chunk09W_decode, chunk09C00_decode, chunk09C01_decode, chunk09C02_decode, chunk09C03_decode, chunk09C04_decode, chunk09C05_decode, chunk09C06_decode, chunk09C07_decode, chunk09C08_decode, chunk09C09_decode, chunk09C10_decode, chunk09C11_decode, chunk09C12_decode, chunk09C13_decode, chunk09C14_decode, chunk09C15_decode, Option.bind_some, Option.map_some]
  rfl

end CGLMP5.CertificateSource
