/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightStageGeometry

/-!
# The actual common triple and right whole-image Cartesian square

Native reassociation changes only the source representation. Transport the existing
right-parenthesized Cartesian square along the actual triple associator, retaining
both maps, the whole nonreduced image, and the original remaining Y diagonal.
This is geometry only; no Tor or weighted comparison is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The common triple's actual right-image square is Cartesian by native reassociation. -/
theorem correspondenceTripleToRightImageIncidence_isPullback :
    IsPullback (correspondenceTripleToRightImageIncidence f g h i z w v)
      (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v)
      (correspondenceRightImageIncidenceInclusion f g h i z w v)
      (correspondenceRightIntermediateImageMap f g h i z w v) := by
  exact (correspondenceRightTripleToImageIncidence_isPullback f g h i z w v).of_iso'
    (correspondenceTripleIncidenceAssoc f g h i z w v) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [correspondenceTripleToRightImageIncidence])
    (by simp [correspondenceTripleIncidenceToRightSupportProduct]) (by simp) (by simp)

/-- Both routes retain the same actual point of the whole right image exterior. -/
@[reassoc]
theorem correspondenceTripleToRightImageIncidence_inclusion :
    correspondenceTripleToRightImageIncidence f g h i z w v ≫
        correspondenceRightImageIncidenceInclusion f g h i z w v =
      correspondenceTripleIncidenceToRightSupportProduct f g h i z w v ≫
        correspondenceRightIntermediateImageMap f g h i z w v :=
  (correspondenceTripleToRightImageIncidence_isPullback f g h i z w v).w

end Stacks.Chow
