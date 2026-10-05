import CGLMP5.AttainmentControls
import CGLMP5.Events
import CGLMP5.Words
import CGLMP5.Root
import CGLMP5.Positivity
import CGLMP5.POVMControls
import CGLMP5.TensorFinite
open CGLMP5
open ContinuousLinearMap
example : eventCoefficientTwo 0 0 0 0 = 2 := by decide
example : Word.mul ⟨[(0,1)],[]⟩ ⟨[(1,1)],[]⟩ ≠ Word.mul ⟨[(1,1)],[]⟩ ⟨[(0,1)],[]⟩ := by decide
example : 3 < mu := mu_gt_three
example : 0 < weightValue 9 := weight_positive 9
example : ¬ Function.Surjective (commonJ : ℂ →L[ℂ] DilationSpace ℂ) := commonJ_not_surjective
example : tensorEuclideanEquiv (Fin 5) (Fin 5)
    (tensorPure (EuclideanSpace.single 0 (1:ℂ)) (EuclideanSpace.single 1 (1:ℂ))) (0,1) = 1 := by simp
#check common_dilation
#check compression_not_multiplicative
#check commonJ_comp_adjoint_ne_one

#check rotatedCommonJ_isometry
#check changing_embedding_changes_effect

-- Strong full-attainment mutation witnesses, checked independently of expected failures.
example : Attainment.explicitStrategy.value = mu := Attainment.explicitStrategy_value
example : ∀ i j, Attainment.Controls.badBell (i,i) (j,j) = Attainment.matrixBell (i,i) (j,j) :=
  Attainment.Controls.badBell_same_compression
example : matrixOp Attainment.Controls.badBell Attainment.state ≠ (mu : ℂ) • Attainment.state :=
  Attainment.Controls.compression_surrogate_rejected
example : Attainment.Controls.wrongBobSpectral ≠ Attainment.localSpectral 1 :=
  Attainment.Controls.wrong_offset_rejected
example : ‖Attainment.Controls.corruptState‖ = 1 := Attainment.Controls.corruptState_norm
example : matrixOp Attainment.matrixBell Attainment.Controls.corruptState ≠
    (mu : ℂ) • Attainment.Controls.corruptState := Attainment.Controls.normalized_schmidt_rejected
