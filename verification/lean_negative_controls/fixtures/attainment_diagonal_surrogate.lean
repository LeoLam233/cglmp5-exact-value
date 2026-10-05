import CGLMP5.AttainmentControls
open CGLMP5 CGLMP5.Attainment CGLMP5.Attainment.Controls
-- badBell has exactly the correct diagonal compression but adds a nonzero off-diagonal output.
-- badBell_same_compression and the actual leakage are separately kernel-checked.
example : matrixOp badBell state = (mu : ℂ) • state := by
  simp only [compression_surrogate_rejected]
