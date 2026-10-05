import CGLMP5.CertificateHeaderProofs
import CGLMP5.SourceDecimalSoundness
import CGLMP5.CertificateData
import CGLMP5.CertificateTerm00
import CGLMP5.CertificateTerm01
import CGLMP5.CertificateTerm02
import CGLMP5.CertificateTerm03
import CGLMP5.CertificateTerm04
import CGLMP5.CertificateTerm05
import CGLMP5.CertificateTerm06
import CGLMP5.CertificateTerm07
import CGLMP5.CertificateTerm08
import CGLMP5.CertificateTerm09
import CGLMP5.CertificateTerm10
import CGLMP5.CertificateTerm11
import CGLMP5.CertificateTerm12
import CGLMP5.CertificateTerm13

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def canonicalPrefix : String := canonicalHeaderPrefix
def sourceChunkTerms : List ChunkTerm := [chunkTerm00, chunkTerm01, chunkTerm02, chunkTerm03, chunkTerm04, chunkTerm05, chunkTerm06, chunkTerm07, chunkTerm08, chunkTerm09, chunkTerm10, chunkTerm11, chunkTerm12, chunkTerm13]
def canonicalSourceBytes : String := canonicalPrefix ++ "  \"terms\": " ++ String.intercalate "\n" (arrayLines TextTerm.renderLines 2 (sourceChunkTerms.map ChunkTerm.toText)) ++ "\n}"
theorem canonical_source_decode : sourceChunkTerms.mapM ChunkTerm.decode = some rawTerms := by
  simp only [sourceChunkTerms, List.mapM_cons, List.mapM_nil, term00_source_decode, term01_source_decode, term02_source_decode, term03_source_decode, term04_source_decode, term05_source_decode, term06_source_decode, term07_source_decode, term08_source_decode, term09_source_decode, term10_source_decode, term11_source_decode, term12_source_decode, term13_source_decode, Option.bind_some]
  rfl

/-- The same data are obtained by parsing the uninterrupted original decimal strings. -/
theorem canonical_text_decode :
    (sourceChunkTerms.map ChunkTerm.toText).mapM TextTerm.decode = some rawTerms := by
  have h00 := ChunkTerm.decode_sound term00_source_decode
  have h01 := ChunkTerm.decode_sound term01_source_decode
  have h02 := ChunkTerm.decode_sound term02_source_decode
  have h03 := ChunkTerm.decode_sound term03_source_decode
  have h04 := ChunkTerm.decode_sound term04_source_decode
  have h05 := ChunkTerm.decode_sound term05_source_decode
  have h06 := ChunkTerm.decode_sound term06_source_decode
  have h07 := ChunkTerm.decode_sound term07_source_decode
  have h08 := ChunkTerm.decode_sound term08_source_decode
  have h09 := ChunkTerm.decode_sound term09_source_decode
  have h10 := ChunkTerm.decode_sound term10_source_decode
  have h11 := ChunkTerm.decode_sound term11_source_decode
  have h12 := ChunkTerm.decode_sound term12_source_decode
  have h13 := ChunkTerm.decode_sound term13_source_decode
  simp only [sourceChunkTerms, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil]
  simp only [h00, h01, h02, h03, h04, h05, h06, h07, h08, h09, h10, h11, h12, h13, Option.bind_some]
  rfl

end CGLMP5.CertificateSource
