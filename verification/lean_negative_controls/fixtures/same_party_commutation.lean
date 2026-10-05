import CGLMP5.Words
open CGLMP5
-- Mutate the ordered same-party product into its reversed word.
example : Word.mul ⟨[(0,1)],[]⟩ ⟨[(1,1)],[]⟩ = Word.mul ⟨[(1,1)],[]⟩ ⟨[(0,1)],[]⟩ := by decide
