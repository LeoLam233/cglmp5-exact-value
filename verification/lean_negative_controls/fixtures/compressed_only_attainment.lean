import CGLMP5.TensorFinite
open CGLMP5
-- Mutate the full product-basis adapter into annihilating an off-diagonal basis vector.
example : tensorEuclideanEquiv (Fin 5) (Fin 5)
    (tensorPure (EuclideanSpace.single 0 (1:ℂ)) (EuclideanSpace.single 1 (1:ℂ))) (0,1) = 0 := by simp
