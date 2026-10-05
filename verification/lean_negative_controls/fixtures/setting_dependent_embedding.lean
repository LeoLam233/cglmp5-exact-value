import CGLMP5.POVMControls
open CGLMP5 ContinuousLinearMap
-- Replace the prescribed fixed inclusion by the setting's defect-unitary-rotated inclusion.
example : compression (rotatedCommonJ halfPOVM)
    (halfPOVM.dilate.effect 0) = halfPOVM.effect 0 := by
  exact halfPOVM.dilate_compression 0
