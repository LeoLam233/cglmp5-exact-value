import CGLMP5.POVMControls
open CGLMP5 ContinuousLinearMap
-- Treat compression of a projection square as the square of its compressed effect.
example : compression (commonJ : ℂ →L[ℂ] DilationSpace ℂ)
    (halfPOVM.dilate.effect 0 * halfPOVM.dilate.effect 0) =
    compression commonJ (halfPOVM.dilate.effect 0) * compression commonJ (halfPOVM.dilate.effect 0) := by
  rfl
