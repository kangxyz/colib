/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Parameters

/-!
# Relative dimension of the native torus

The actual comparison with relative affine space gives dimension one for the
native affine line. The positive Laurent open and base change preserve that
dimension on the existing multiplicative group.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

private theorem additiveGroup_smoothOfRelativeDimension_one :
    SmoothOfRelativeDimension 1 (additiveGroup.{u} ↘ Spec (.of (ULift.{u} ℤ))) := by
  let S := Spec (.of (ULift.{u} ℤ))
  let p := AffineSpace (ULift.{u} Unit) S ↘ S
  have hp : SmoothOfRelativeDimension 1 p := by
    change SmoothOfRelativeDimension 1 (AffineSpace (ULift.{u} Unit) S ↘ S)
    apply AffineSpace.smoothOfRelativeDimension_of_card_eq
    simp
  have h : IsPullback additiveGroupAffineSpaceIso.{u}.hom (additiveGroup ↘ S) p (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id]
      exact additiveGroupAffineSpaceIso_hom_over.{u}⟩
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) h hp

/-- The projection of the native multiplicative group is smooth of relative dimension one. -/
instance multiplicativeGroupBaseChange_smoothOfRelativeDimension_one (S : Scheme.{u}) :
    SmoothOfRelativeDimension 1 (multiplicativeGroupBaseChange S ↘ S) := by
  let π := (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
  let a := (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
  let : SmoothOfRelativeDimension 1 a := additiveGroup_smoothOfRelativeDimension_one
  have he : multiplicativeGroupToAdditive.{u} ≫ a = π := multiplicativeGroupToAdditive_over
  let : SmoothOfRelativeDimension 1 π := he ▸
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (multiplicativeGroupToAdditive ≫ a))
  change SmoothOfRelativeDimension 1 (pullback.snd π (specULiftZIsTerminal.from S))
  infer_instance

end AlgebraicGeometry
