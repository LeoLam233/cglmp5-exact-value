import CGLMP5.Events
open CGLMP5
-- Mutate the second outcome in the coefficient anchor while retaining the unshifted value.
example : eventCoefficientTwo 0 0 0 1 = 2 := by decide
