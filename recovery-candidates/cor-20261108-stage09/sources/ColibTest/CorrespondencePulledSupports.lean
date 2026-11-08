/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.PulledSupports

/-! Tests retain arbitrary schemes and the actual, possibly nonreduced, pulled subschemes. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

example : correspondenceLeftPulledIdeal f g h z =
    (integralComponentAt z).comap
      (pullback.fst (pullback.snd f g) (pullback.fst g h)) := rfl

example : correspondenceRightPulledIdeal f g h w =
    (integralComponentAt w).comap
      (pullback.snd (pullback.snd f g) (pullback.fst g h)) := rfl

example : correspondenceLeftPulledInclusion f g h z =
    (correspondenceLeftPulledIdeal f g h z).subschemeι := rfl

example : correspondenceRightPulledInclusion f g h w =
    (correspondenceRightPulledIdeal f g h w).subschemeι := rfl

example : IsClosedImmersion (correspondenceLeftPulledInclusion f g h z) := inferInstance

example : IsClosedImmersion (correspondenceRightPulledInclusion f g h w) := inferInstance

example : correspondenceIncidenceToLeftPulled f g h z w ≫
    correspondenceLeftPulledInclusion f g h z =
      correspondenceIncidenceInclusion f g h z w := by simp

example : correspondenceIncidenceToRightPulled f g h z w ≫
    correspondenceRightPulledInclusion f g h w =
      correspondenceIncidenceInclusion f g h z w := by simp

example : correspondenceIncidenceToLeftPulled f g h z w ≫
    correspondenceLeftPulledProjection f g h z = pullback.fst _ _ := by
  simp only [correspondenceIncidenceToLeftPulled, correspondenceLeftPulledProjection,
    Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]

example : correspondenceIncidenceToRightPulled f g h z w ≫
    correspondenceRightPulledProjection f g h w = pullback.snd _ _ := by
  simp only [correspondenceIncidenceToRightPulled, correspondenceRightPulledProjection,
    Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]

example (t : correspondenceIncidence f g h z w) :
    correspondenceLeftPulledInclusion f g h z
      (correspondenceIncidenceToLeftPulled f g h z w t) =
        correspondenceIncidenceInclusion f g h z w t :=
  congrArg (fun m : correspondenceIncidence f g h z w ⟶ correspondenceTripleProduct f g h =>
    m t) (correspondenceIncidenceToLeftPulled_inclusion f g h z w)

example (t : correspondenceIncidence f g h z w) :
    correspondenceRightPulledInclusion f g h w
      (correspondenceIncidenceToRightPulled f g h z w t) =
        correspondenceIncidenceInclusion f g h z w t :=
  congrArg (fun m : correspondenceIncidence f g h z w ⟶ correspondenceTripleProduct f g h =>
    m t) (correspondenceIncidenceToRightPulled_inclusion f g h z w)

example : IsPullback (correspondenceLeftPulledInclusion f g h z)
    (correspondenceLeftPulledProjection f g h z)
    (pullback.fst (pullback.snd f g) (pullback.fst g h))
    (integralComponentAt z).subschemeι := isPullback_correspondenceLeftPulled f g h z

example : IsPullback (correspondenceRightPulledInclusion f g h w)
    (correspondenceRightPulledProjection f g h w)
    (pullback.snd (pullback.snd f g) (pullback.fst g h))
    (integralComponentAt w).subschemeι := isPullback_correspondenceRightPulled f g h w

example : IsPullback (correspondenceIncidenceToLeftPulled f g h z w)
    (correspondenceIncidenceToRightPulled f g h z w)
    (correspondenceLeftPulledInclusion f g h z)
    (correspondenceRightPulledInclusion f g h w) :=
  isPullback_correspondencePulledIncidence f g h z w

example : (correspondenceIncidenceInclusion f g h z w).ker =
    correspondenceLeftPulledIdeal f g h z ⊔ correspondenceRightPulledIdeal f g h w :=
  correspondenceIncidenceInclusion_ker f g h z w
