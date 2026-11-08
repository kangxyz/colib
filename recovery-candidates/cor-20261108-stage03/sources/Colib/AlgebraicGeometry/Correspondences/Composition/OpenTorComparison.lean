/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.OpenPulledGeometry
public import Colib.AlgebraicGeometry.Intersection.OpenStalkComparison

/-!
# Actual incidence Tor and pulled-support Tor under open restriction

New recovery reconstruction, 2026-11-08. Uncompiled and not a byte-identical recovery
of the lost next-stage draft. The retained actual module definitions were checked
against the independently recovered exact StalkModules and PulledStalkModules.

Both conclusions use the existing actual stalk modules. The proof applies native
open-stalk Tor transport to the actual constructed squares. It supplies all point
transports and does not assume an abstract Tor comparison or replace ideal schemes.

Source background: motivic@a6805c4,
Correspondences/Composition/Incidence/GlobalAmbientTorComparison.lean.
The native Tor transport is Stacks RingTheory.TorIndependence.torRestrictIso.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow.CorrespondenceOpenNeighborhoods

variable {S X Y Z X' Y' Z' : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (uX : X' ⟶ X) (uY : Y' ⟶ Y) (uZ : Z' ⟶ Z)
  [IsOpenImmersion uX] [IsOpenImmersion uY] [IsOpenImmersion uZ]
  (z : pullback f g) (w : pullback g h)
  (z' : pullback (uX ≫ f) (uY ≫ g)) (w' : pullback (uY ≫ g) (uZ ≫ h))
  (vI : (integralComponentAt z').subscheme ⟶ (integralComponentAt z).subscheme)
  (vJ : (integralComponentAt w').subscheme ⟶ (integralComponentAt w).subscheme)
  [IsOpenImmersion vI] [IsOpenImmersion vJ]
  (hi : vI ≫ (integralComponentAt z).subschemeι =
    (integralComponentAt z').subschemeι ≫ productMap f g uX uY)
  (hj : vJ ≫ (integralComponentAt w).subschemeι =
    (integralComponentAt w').subschemeι ≫ productMap g h uY uZ)
  (t' : correspondenceIncidence (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w') (n : ℕ)

/-- The actual ambient Tor length is invariant under the constructed open neighborhood. -/
theorem incidenceTor_length_eq_open :
    Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h z w (incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj t')))
      (((Tor (ModuleCat ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h z w (incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj t')))) n).obj
        (correspondenceIncidenceSupportStalkModule f g h z w (incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj t'))).obj
        (correspondenceIncidenceTripleStalkModule f g h z w (incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj t'))) =
    Module.length ((correspondenceIntersectionAmbient (uX ≫ f) (uY ≫ g) (uZ ≫ h)).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t'))
      (((Tor (ModuleCat ((correspondenceIntersectionAmbient (uX ≫ f) (uY ≫ g) (uZ ≫ h)).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t'))) n).obj
        (correspondenceIncidenceSupportStalkModule (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t')).obj
        (correspondenceIncidenceTripleStalkModule (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t')) := by
  let e := incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj
  have hT : tripleMap f g h uX uY uZ
      (correspondenceIncidenceInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t') =
      correspondenceIncidenceInclusion f g h z w (e t') :=
    (congrArg (fun m => m t')
      (incidenceMap_inclusion f g h uX uY uZ z w z' w' vI vJ hi hj)).symm
  have hP : supportProductMap f g h uX uY uZ z w z' w' vI vJ hi hj
      (correspondenceIncidenceToSupportProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t') =
      correspondenceIncidenceToSupportProduct f g h z w (e t') :=
    (congrArg (fun m => m t')
      (incidenceMap_toSupportProduct f g h uX uY uZ z w z' w' vI vJ hi hj)).symm
  have hA : ambientMap f g h uX uY uZ
      (correspondenceIncidenceAmbientInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t') =
      correspondenceIncidenceAmbientInclusion f g h z w (e t') := by
    change (correspondenceIncidenceInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' ≫
      correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) ≫
        ambientMap f g h uX uY uZ) t' = _
    rw [← tripleMap_inclusion, ← Category.assoc, ← incidenceMap_inclusion]
    rfl
  have hy := hA.trans ((correspondenceIncidence_ambient_point_eq f g h z w (e t')).trans
    (congrArg (correspondenceSupportProductInclusion f g h z w) hP).symm)
  have hz := hA.trans (congrArg (correspondenceTripleInclusion f g h) hT).symm
  have H := Scheme.length_torStalks_eq_of_openSquares
    (correspondenceSupportProductInclusion f g h z w)
    (correspondenceTripleInclusion f g h)
    (correspondenceSupportProductInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w')
    (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h))
    (ambientMap f g h uX uY uZ)
    (supportProductMap f g h uX uY uZ z w z' w' vI vJ hi hj)
    (tripleMap f g h uX uY uZ)
    (supportProductMap_inclusion f g h uX uY uZ z w z' w' vI vJ hi hj)
    (tripleMap_inclusion f g h uX uY uZ)
    (correspondenceIncidenceAmbientInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t')
    (correspondenceIncidenceToSupportProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t')
    (correspondenceIncidenceInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t')
    (correspondenceIncidence_ambient_point_eq (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t')
    rfl hy hz n
  simpa only [hA, hP, hT, correspondenceIncidenceSupportStalkModule,
    correspondenceIncidenceTripleStalkModule, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] using H

/-- The actual two pulled-support Tor modules retain their lengths under the same open
restriction, at the same actual incidence point. -/
theorem pulledTor_length_eq_open :
    Module.length ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w (incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj t')))
      (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w (incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj t')))) n).obj
        (correspondenceIncidenceLeftPulledStalkModule f g h z w (incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj t'))).obj
        (correspondenceIncidenceRightPulledStalkModule f g h z w (incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj t'))) =
    Module.length ((correspondenceTripleProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h)).presheaf.stalk
      (correspondenceIncidenceInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t'))
      (((Tor (ModuleCat ((correspondenceTripleProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h)).presheaf.stalk
      (correspondenceIncidenceInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t'))) n).obj
        (correspondenceIncidenceLeftPulledStalkModule (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t')).obj
        (correspondenceIncidenceRightPulledStalkModule (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t')) := by
  let e := incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj
  have hT : tripleMap f g h uX uY uZ
      (correspondenceIncidenceInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t') =
      correspondenceIncidenceInclusion f g h z w (e t') :=
    (congrArg (fun m => m t')
      (incidenceMap_inclusion f g h uX uY uZ z w z' w' vI vJ hi hj)).symm
  have hL : leftPulledMap f g h uX uY uZ z z' vI hi
      (correspondenceIncidenceToLeftPulled (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t') =
      correspondenceIncidenceToLeftPulled f g h z w (e t') :=
    (congrArg (fun m => m t')
      (incidenceMap_toLeftPulled f g h uX uY uZ z w z' w' vI vJ hi hj)).symm
  have hR : rightPulledMap f g h uX uY uZ w w' vJ hj
      (correspondenceIncidenceToRightPulled (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t') =
      correspondenceIncidenceToRightPulled f g h z w (e t') :=
    (congrArg (fun m => m t')
      (incidenceMap_toRightPulled f g h uX uY uZ z w z' w' vI vJ hi hj)).symm
  have hy := hT.trans ((correspondenceIncidence_leftPulled_point_eq f g h z w (e t')).trans
    (congrArg (correspondenceLeftPulledInclusion f g h z) hL).symm)
  have hz := hT.trans ((correspondenceIncidence_rightPulled_point_eq f g h z w (e t')).trans
    (congrArg (correspondenceRightPulledInclusion f g h w) hR).symm)
  have H := Scheme.length_torStalks_eq_of_openSquares
    (correspondenceLeftPulledInclusion f g h z)
    (correspondenceRightPulledInclusion f g h w)
    (correspondenceLeftPulledInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z')
    (correspondenceRightPulledInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) w')
    (tripleMap f g h uX uY uZ)
    (leftPulledMap f g h uX uY uZ z z' vI hi)
    (rightPulledMap f g h uX uY uZ w w' vJ hj)
    (leftPulledMap_inclusion f g h uX uY uZ z z' vI hi)
    (rightPulledMap_inclusion f g h uX uY uZ w w' vJ hj)
    (correspondenceIncidenceInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t')
    (correspondenceIncidenceToLeftPulled (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t')
    (correspondenceIncidenceToRightPulled (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t')
    (correspondenceIncidence_leftPulled_point_eq (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t')
    (correspondenceIncidence_rightPulled_point_eq (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t')
    hy hz n
  simpa only [hT, hL, hR, correspondenceIncidenceLeftPulledStalkModule,
    correspondenceIncidenceRightPulledStalkModule] using H

end Stacks.Chow.CorrespondenceOpenNeighborhoods
