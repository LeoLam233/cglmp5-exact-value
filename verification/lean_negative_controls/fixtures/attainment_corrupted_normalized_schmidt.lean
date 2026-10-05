import CGLMP5.AttainmentControls
open CGLMP5 CGLMP5.Attainment CGLMP5.Attainment.Controls
-- Add1 to the central Schmidt amplitude, genuinely re-normalize, and falsely claim attainment.
-- corruptState_norm is separately kernel-checked, so failure is not a normalization shortcut.
example : matrixOp matrixBell corruptState = (mu : ℂ) • corruptState := by
  simp only [normalized_schmidt_rejected]
