import CGLMP5.CertificateSource

/-- Executable readback only. The kernel decoding theorem is proved independently. -/
def main : IO Unit := IO.print CGLMP5.CertificateSource.canonicalSourceBytes
