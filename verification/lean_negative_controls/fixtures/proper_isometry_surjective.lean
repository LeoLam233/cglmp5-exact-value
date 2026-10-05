import CGLMP5.POVMControls
open CGLMP5 ContinuousLinearMap
-- Exchange the two sides of the fixed isometry relation.
example : (commonJ : ℂ →L[ℂ] DilationSpace ℂ) ∘L commonJ.adjoint = 1 := by
  exact commonJ_isometry (H := ℂ)
