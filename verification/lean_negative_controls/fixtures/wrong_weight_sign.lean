import CGLMP5.Positivity
open CGLMP5
-- Reverse the sign of one actual-embedding certificate weight.
example : 0 < -weightValue 9 := by linarith [weight_positive 9]
