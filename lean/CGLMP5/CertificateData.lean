import CGLMP5.CertificateTerm00Data
import CGLMP5.CertificateTerm01Data
import CGLMP5.CertificateTerm02Data
import CGLMP5.CertificateTerm03Data
import CGLMP5.CertificateTerm04Data
import CGLMP5.CertificateTerm05Data
import CGLMP5.CertificateTerm06Data
import CGLMP5.CertificateTerm07Data
import CGLMP5.CertificateTerm08Data
import CGLMP5.CertificateTerm09Data
import CGLMP5.CertificateTerm10Data
import CGLMP5.CertificateTerm11Data
import CGLMP5.CertificateTerm12Data
import CGLMP5.CertificateTerm13Data
import CGLMP5.CertificateEmbeddingData

namespace CGLMP5.CertificateSource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def rawTerms : List RawTerm := [term00, term01, term02, term03, term04, term05, term06, term07, term08, term09, term10, term11, term12, term13]

theorem rawTerms_length : rawTerms.length = 14 := by decide

theorem rawTerms_valid : ∀ t ∈ rawTerms, t.valid := by
  simp only [rawTerms, List.mem_cons, List.not_mem_nil, or_false]
  intro t ht
  rcases ht with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · subst t; exact term00_valid
  · subst t; exact term01_valid
  · subst t; exact term02_valid
  · subst t; exact term03_valid
  · subst t; exact term04_valid
  · subst t; exact term05_valid
  · subst t; exact term06_valid
  · subst t; exact term07_valid
  · subst t; exact term08_valid
  · subst t; exact term09_valid
  · subst t; exact term10_valid
  · subst t; exact term11_valid
  · subst t; exact term12_valid
  · subst t; exact term13_valid

end CGLMP5.CertificateSource
