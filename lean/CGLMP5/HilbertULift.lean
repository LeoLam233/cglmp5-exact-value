import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Lawful Hilbert structure on universe lifts

The inherited norm and scalar action are retained; the inner product is pulled back by `down`.
-/

noncomputable section
universe u v w

namespace CGLMP5

instance uliftInnerProductSpace {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] : InnerProductSpace 𝕜 (ULift.{w} H) where
  __ := (inferInstance : NormedSpace 𝕜 (ULift.{w} H))
  inner x y := inner 𝕜 x.down y.down
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner x.down
  conj_inner_symm x y := inner_conj_symm _ _
  add_left x y z := inner_add_left _ _ _
  smul_left x y r := inner_smul_left _ _ _

@[simp] theorem ulift_inner {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (x y : ULift.{w} H) :
    inner 𝕜 x y = inner 𝕜 x.down y.down := rfl

end CGLMP5
