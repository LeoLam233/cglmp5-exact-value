import CGLMP5.AttainmentControls
open CGLMP5 CGLMP5.Attainment CGLMP5.Attainment.Controls
-- Mutate Bob beta0 from1/4 to0. The positive control proves the resulting spectral operator differs.
example : wrongBobSpectral = localSpectral 1 := by
  simp only [wrong_offset_rejected]
