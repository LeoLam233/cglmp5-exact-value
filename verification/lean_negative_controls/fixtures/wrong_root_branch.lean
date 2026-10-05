import CGLMP5.Root
open CGLMP5
-- Select the opposite side of the proved root-isolation boundary.
example : mu < 3 := by linarith [mu_gt_three]
