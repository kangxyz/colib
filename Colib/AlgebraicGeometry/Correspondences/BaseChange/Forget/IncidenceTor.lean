/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.Forget.SupportProduct
public import Colib.AlgebraicGeometry.Correspondences.Composition.GenericTorLength
public import Colib.AlgebraicGeometry.Intersection.OpenStalkComparison

/-!
# Every ambient Tor length after forgetting an unramified base

The actual ambient, support-product and triple-product open immersions identify
both native stalk modules. This proves equality in every homological degree,
including infinite lengths, with all actual point transports retained. No field,
smoothness, regularity, finite-length or correspondence-admissibility assumption
is required. The base map is separated, formally unramified and locally of finite type.

Adapted from motivic `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/BaseChange/Forget/IncidenceTor.lean`.
The proof applies Colib's existing native open-square Tor comparison as in
`Correspondences/Composition/OpenTorComparison.lean`; it introduces no new Tor model.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {S T X Y Z : Scheme.{u}} (r : T ⟶ S)
  (f : X ⟶ T) (g : Y ⟶ T) (h : Z ⟶ T)
  [IsSeparated r] [FormallyUnramified r] [LocallyOfFiniteType r]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The actual ambient Tor lengths agree in every degree, including infinite lengths. -/
theorem forgetBaseIncidenceTor_length (t : correspondenceIncidence f g h z w) (n : ℕ) :
    Module.length
      ((correspondenceIntersectionAmbient (f ≫ r) (g ≫ r) (h ≫ r)).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion (f ≫ r) (g ≫ r) (h ≫ r)
          (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w)
          (forgetBaseIncidenceMap r f g h z w t)))
      (correspondenceIncidenceTor (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w)
        (forgetBaseIncidenceMap r f g h z w t) n) =
    Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h z w t))
      (correspondenceIncidenceTor f g h z w t n) := by
  let e := forgetBaseIncidenceMap r f g h z w
  have hT : forgetBaseTripleMap r f g h
      (correspondenceIncidenceInclusion f g h z w t) =
      correspondenceIncidenceInclusion (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) (e t) :=
    (congrArg (fun m :
      correspondenceIncidence f g h z w ⟶
        correspondenceTripleProduct (f ≫ r) (g ≫ r) (h ≫ r) => m t)
      (forgetBaseIncidenceMap_inclusion r f g h z w)).symm
  have hP : forgetBaseSupportProductMap r f g h z w
      (correspondenceIncidenceToSupportProduct f g h z w t) =
      correspondenceIncidenceToSupportProduct (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) (e t) :=
    (congrArg (fun m :
      correspondenceIncidence f g h z w ⟶
        correspondenceSupportProduct (f ≫ r) (g ≫ r) (h ≫ r)
          (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) => m t)
      (forgetBaseIncidenceMap_supportProduct r f g h z w)).symm
  have hA : forgetBaseAmbientMap r f g h
      (correspondenceIncidenceAmbientInclusion f g h z w t) =
      correspondenceIncidenceAmbientInclusion (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) (e t) := by
    have hSquare := congrArg (fun m :
      correspondenceTripleProduct f g h ⟶
        correspondenceIntersectionAmbient (f ≫ r) (g ≫ r) (h ≫ r) =>
          m (correspondenceIncidenceInclusion f g h z w t))
      (forgetBaseTripleInclusion_square r f g h)
    simpa only [correspondenceIncidenceAmbientInclusion, Scheme.Hom.comp_apply] using
      hSquare.symm.trans (congrArg (correspondenceTripleInclusion (f ≫ r) (g ≫ r) (h ≫ r)) hT)
  have hy := hA.trans ((correspondenceIncidence_ambient_point_eq (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) (e t)).trans
    (congrArg (correspondenceSupportProductInclusion (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w)) hP).symm)
  have hz := hA.trans (congrArg (correspondenceTripleInclusion (f ≫ r) (g ≫ r) (h ≫ r)) hT).symm
  have H := Scheme.length_torStalks_eq_of_openSquares
    (correspondenceSupportProductInclusion (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w))
    (correspondenceTripleInclusion (f ≫ r) (g ≫ r) (h ≫ r))
    (correspondenceSupportProductInclusion f g h z w)
    (correspondenceTripleInclusion f g h)
    (forgetBaseAmbientMap r f g h)
    (forgetBaseSupportProductMap r f g h z w)
    (forgetBaseTripleMap r f g h)
    (forgetBaseSupportProduct_square r f g h z w)
    (forgetBaseTripleInclusion_square r f g h)
    (correspondenceIncidenceAmbientInclusion f g h z w t)
    (correspondenceIncidenceToSupportProduct f g h z w t)
    (correspondenceIncidenceInclusion f g h z w t)
    (correspondenceIncidence_ambient_point_eq f g h z w t)
    rfl hy hz n
  -- Keep the three point indices together while rewriting. Rewriting inside the
  -- raw ring/module instances separately would introduce dependent transports.
  let lengthAt (x : correspondenceIntersectionAmbient (f ≫ r) (g ≫ r) (h ≫ r))
      (y : correspondenceSupportProduct (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w))
      (q : correspondenceTripleProduct (f ≫ r) (g ≫ r) (h ≫ r))
      (hy : x = correspondenceSupportProductInclusion (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) y)
      (hq : x = correspondenceTripleInclusion (f ≫ r) (g ≫ r) (h ≫ r) q) : ℕ∞ :=
    Module.length ((correspondenceIntersectionAmbient (f ≫ r) (g ≫ r) (h ≫ r)).presheaf.stalk x)
      (((Tor (ModuleCat
        ((correspondenceIntersectionAmbient (f ≫ r) (g ≫ r) (h ≫ r)).presheaf.stalk x)) n).obj
        ((ModuleCat.restrictScalars
          (((correspondenceIntersectionAmbient (f ≫ r) (g ≫ r) (h ≫ r)).presheaf.stalkCongr
            (.of_eq hy)).hom ≫
            (correspondenceSupportProductInclusion (f ≫ r) (g ≫ r) (h ≫ r)
              (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w)).stalkMap y).hom).obj
          (ModuleCat.of ((correspondenceSupportProduct (f ≫ r) (g ≫ r) (h ≫ r)
            (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w)).presheaf.stalk y)
            ((correspondenceSupportProduct (f ≫ r) (g ≫ r) (h ≫ r)
              (forgetBaseProductMap r f g z)
              (forgetBaseProductMap r g h w)).presheaf.stalk y)))).obj
        ((ModuleCat.restrictScalars
          (((correspondenceIntersectionAmbient (f ≫ r) (g ≫ r) (h ≫ r)).presheaf.stalkCongr
            (.of_eq hq)).hom ≫
            (correspondenceTripleInclusion (f ≫ r) (g ≫ r) (h ≫ r)).stalkMap q).hom).obj
          (ModuleCat.of ((correspondenceTripleProduct (f ≫ r) (g ≫ r) (h ≫ r)).presheaf.stalk q)
            ((correspondenceTripleProduct (f ≫ r) (g ≫ r) (h ≫ r)).presheaf.stalk q))))
  change lengthAt
    (forgetBaseAmbientMap r f g h
      (correspondenceIncidenceAmbientInclusion f g h z w t))
    (forgetBaseSupportProductMap r f g h z w
      (correspondenceIncidenceToSupportProduct f g h z w t))
    (forgetBaseTripleMap r f g h
      (correspondenceIncidenceInclusion f g h z w t))
    hy hz = _ at H
  simp only [hA, hP, hT] at H
  have hRefl {P T : Scheme.{u}} (i : T ⟶ P) (q : T) :
      (((P.presheaf.stalkCongr (.of_eq (rfl : i q = i q))).hom ≫ i.stalkMap q).hom) =
        (i.stalkMap q).hom := by
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      Category.id_comp]
  dsimp only [lengthAt] at H
  rw [hRefl (correspondenceTripleInclusion (f ≫ r) (g ≫ r) (h ≫ r))
      (correspondenceIncidenceInclusion (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) (e t)),
    hRefl (correspondenceTripleInclusion f g h)
      (correspondenceIncidenceInclusion f g h z w t)] at H
  exact H

end Stacks.Chow
