/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.PulledSupports
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Actual pulled-support stalk modules at incidence points

These are the two literal local rings of the native pulled ideal subschemes,
restricted along their actual stalk maps to the actual triple-product stalk.
Point transport uses the proved inclusion equations. In particular, neither
pulled subscheme is replaced by its reduction.

Implementation provenance: `motivic_source_a6805c4`,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Incidence/GlobalAmbientTorComparison.lean`.
The local source modules are exposed below Tor and its affine comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The actual left pulled-support point lies over the actual incidence image. -/
theorem correspondenceIncidence_leftPulled_point_eq (t : correspondenceIncidence f g h z w) :
    correspondenceIncidenceInclusion f g h z w t =
      correspondenceLeftPulledInclusion f g h z
        (correspondenceIncidenceToLeftPulled f g h z w t) :=
  (congrArg (fun m : correspondenceIncidence f g h z w ⟶ correspondenceTripleProduct f g h =>
    m t) (correspondenceIncidenceToLeftPulled_inclusion f g h z w)).symm

/-- The actual right pulled-support point lies over the same incidence image. -/
theorem correspondenceIncidence_rightPulled_point_eq (t : correspondenceIncidence f g h z w) :
    correspondenceIncidenceInclusion f g h z w t =
      correspondenceRightPulledInclusion f g h w
        (correspondenceIncidenceToRightPulled f g h z w t) :=
  (congrArg (fun m : correspondenceIncidence f g h z w ⟶ correspondenceTripleProduct f g h =>
    m t) (correspondenceIncidenceToRightPulled_inclusion f g h z w)).symm

/-- The full left pulled-support local ring with its actual triple-stalk action. -/
abbrev correspondenceIncidenceLeftPulledStalkModule (t : correspondenceIncidence f g h z w) :
    ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w t)) :=
  (ModuleCat.restrictScalars
    (((correspondenceTripleProduct f g h).presheaf.stalkCongr
      (.of_eq (correspondenceIncidence_leftPulled_point_eq f g h z w t))).hom ≫
        (correspondenceLeftPulledInclusion f g h z).stalkMap
          (correspondenceIncidenceToLeftPulled f g h z w t)).hom).obj
    (ModuleCat.of
      ((correspondenceLeftPulledIdeal f g h z).subscheme.presheaf.stalk
        (correspondenceIncidenceToLeftPulled f g h z w t))
      ((correspondenceLeftPulledIdeal f g h z).subscheme.presheaf.stalk
        (correspondenceIncidenceToLeftPulled f g h z w t)))

/-- The full right pulled-support local ring with its actual triple-stalk action. -/
abbrev correspondenceIncidenceRightPulledStalkModule (t : correspondenceIncidence f g h z w) :
    ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w t)) :=
  (ModuleCat.restrictScalars
    (((correspondenceTripleProduct f g h).presheaf.stalkCongr
      (.of_eq (correspondenceIncidence_rightPulled_point_eq f g h z w t))).hom ≫
        (correspondenceRightPulledInclusion f g h w).stalkMap
          (correspondenceIncidenceToRightPulled f g h z w t)).hom).obj
    (ModuleCat.of
      ((correspondenceRightPulledIdeal f g h w).subscheme.presheaf.stalk
        (correspondenceIncidenceToRightPulled f g h z w t))
      ((correspondenceRightPulledIdeal f g h w).subscheme.presheaf.stalk
        (correspondenceIncidenceToRightPulled f g h z w t)))

end Stacks.Chow
