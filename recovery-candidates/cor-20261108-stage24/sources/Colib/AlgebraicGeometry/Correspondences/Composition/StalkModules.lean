/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.Diagonal
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Actual local structure-ring modules of the correspondence incidence

These are the literal local rings of the product support and triple product,
restricted along their actual maps to the four-factor ambient scheme. Transport
is only between the two proved-equal ambient images of the same incidence point.
No Tor sheaf, regularity, coherence or multiplicity is needed to define them.

Implementation provenance: `motivic_source_a6805c4`,
`Motivic/Aglib/AlgebraicGeometry/Intersection/StalkModules.lean`, specialized to
the existing actual incidence diagram. Extracted below the Tor-sheaf comparison
so actual affine-coordinate consumers do not import unrelated sheaf suppliers.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The actual incidence closed subscheme of the four-factor ambient product. -/
abbrev correspondenceIncidenceAmbientInclusion :
    correspondenceIncidence f g h z w ⟶ correspondenceIntersectionAmbient f g h :=
  correspondenceIncidenceInclusion f g h z w ≫ correspondenceTripleInclusion f g h

instance isClosedImmersion_correspondenceIncidenceAmbientInclusion [IsSeparated g] :
    IsClosedImmersion (correspondenceIncidenceAmbientInclusion f g h z w) := by
  dsimp only [correspondenceIncidenceAmbientInclusion]
  infer_instance

/-- The two actual images of an incidence point agree in the ambient scheme. -/
theorem correspondenceIncidence_ambient_point_eq (t : correspondenceIncidence f g h z w) :
    correspondenceTripleInclusion f g h (correspondenceIncidenceInclusion f g h z w t) =
      correspondenceSupportProductInclusion f g h z w
        (correspondenceIncidenceToSupportProduct f g h z w t) := by
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun k : correspondenceIncidence f g h z w ⟶
        correspondenceIntersectionAmbient f g h => k t)
      (correspondenceIncidence_ambient_comm f g h z w)

/-- The actual support-product local ring, restricted along its transported actual stalk map. -/
abbrev correspondenceIncidenceSupportStalkModule (t : correspondenceIncidence f g h z w) :
    ModuleCat ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h z w t)) :=
  (ModuleCat.restrictScalars
    (((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
      (.of_eq (correspondenceIncidence_ambient_point_eq f g h z w t))).hom ≫
        (correspondenceSupportProductInclusion f g h z w).stalkMap
          (correspondenceIncidenceToSupportProduct f g h z w t)).hom).obj
    (ModuleCat.of
      ((correspondenceSupportProduct f g h z w).presheaf.stalk
        (correspondenceIncidenceToSupportProduct f g h z w t))
      ((correspondenceSupportProduct f g h z w).presheaf.stalk
        (correspondenceIncidenceToSupportProduct f g h z w t)))

/-- The actual triple-product local ring, restricted along the literal triple-inclusion map. -/
abbrev correspondenceIncidenceTripleStalkModule (t : correspondenceIncidence f g h z w) :
    ModuleCat ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h z w t)) :=
  (ModuleCat.restrictScalars
    ((correspondenceTripleInclusion f g h).stalkMap
      (correspondenceIncidenceInclusion f g h z w t)).hom).obj
    (ModuleCat.of
      ((correspondenceTripleProduct f g h).presheaf.stalk
        (correspondenceIncidenceInclusion f g h z w t))
      ((correspondenceTripleProduct f g h).presheaf.stalk
        (correspondenceIncidenceInclusion f g h z w t)))

end Stacks.Chow
