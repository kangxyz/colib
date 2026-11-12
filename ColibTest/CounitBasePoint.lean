/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.CounitBasePoint
import Colib.AlgebraicGeometry.Sites.Smooth.Frobenius
import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} [IsAffine S] (Y : SmoothSite S)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ Y.left)

local instance : IsAffine (SmoothSite.base S).left := inferInstanceAs (IsAffine S)

-- The native source isomorphism's inverse retains the actual unit and scheme map.
-- This representative statement does not assume that Y is affine.
example (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : EtaleSeparatedFiniteType S) (A : SmoothSite.EtaleNeighborhood Y ξ)
    (f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶
      (toSmoothSite (SmoothSite.base S)).obj U) :
    (pointSmallEtale (ξ ≫ Y.hom)).toPresheafFiber ((toSmallEtale S).obj U)
        (etaleNeighborhoodMapLift Y ξ U A f) G.obj ≫
      (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).inv.app G =
    ((etaleExtendRestrictAdjunction (SmoothSite.base S)).unit.app
        ((sheafEquivSmallEtale (SmoothSite.base S)).inverse.obj G)).hom.app (op U) ≫
      ((fullSmallEtaleExtend (SmoothSite.base S)).obj G).obj.map f.op ≫
        SmoothSite.toEtaleNeighborhoodValue Y ξ A
          ((fullSmallEtaleExtend (SmoothSite.base S)).obj G).obj :=
  nativeBaseGerm_fullSmallEtaleExtendNativeBaseSheafFiberIso_inv Y ξ G U A f

-- The displayed structure map is literally Y.hom, not an assumed comparison map.
example [IsAffine Y.left] (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    let p : Y ⟶ SmoothSite.base S := SmoothSite.homMk Y.hom (by
      change Y.hom ≫ 𝟙 S = Y.hom
      exact Category.comp_id _)
    (fullSmallEtaleRestrictNeighborhoodIso (SmoothSite.base S) (ξ ≫ Y.hom) F).hom ≫
      (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).inv.app
        ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F) ≫
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
        ((fullSmallEtaleAdjunction (SmoothSite.base S)).counit.app F).hom =
    SmoothSite.etaleNeighborhoodValuePullback p rfl F.obj := by
  dsimp only
  exact fullSmallEtale_counit_eq_structuralNeighborhoodPullback Y ξ _ rfl F

example [IsAffine Y.left] (p : Y ⟶ SmoothSite.base S)
    (h : ξ ≫ p.left = ξ ≫ Y.hom)
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    IsIso ((SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
      ((fullSmallEtaleAdjunction (SmoothSite.base S)).counit.app F).hom) ↔
    IsIso (SmoothSite.etaleNeighborhoodValuePullback p h F.obj) :=
  isIso_fullSmallEtale_counit_iff_structuralNeighborhoodPullback Y ξ p h F

-- Original coefficient morphisms commute with the original marked pullback.
example [IsAffine Y.left] {X : SmoothSite S} [IsAffine X.left]
    (f : X ⟶ Y) (ζ : Spec (.of Ω) ⟶ X.left) (h : ζ ≫ f.left = ξ)
    {F G : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (a : F ⟶ G) :
    (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map a ≫
      SmoothSite.etaleNeighborhoodValuePullback f h G =
    SmoothSite.etaleNeighborhoodValuePullback f h F ≫
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} X ζ).presheafFiber.map a :=
  SmoothSite.etaleNeighborhoodValuePullback_naturality f h a

-- Naturality is for the source isomorphism itself, for every full-small coefficient sheaf.
example [IsAffine Y.left] {X : SmoothSite S} [IsAffine X.left]
    (f : X ⟶ Y) (ζ : Spec (.of Ω) ⟶ X.left) (h : ζ ≫ f.left = ξ)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).inv.app G ≫
      SmoothSite.etaleNeighborhoodValuePullback f h
        ((fullSmallEtaleExtend (SmoothSite.base S)).obj G).obj =
    eqToHom (congrArg (fun z ↦ (pointSmallEtale z).sheafFiber.obj G)
        (SmoothSite.markedSmooth_baseMarking_eq Y ξ f ζ h).symm) ≫
      (fullSmallEtaleExtendNativeBaseSheafFiberIso X ζ).inv.app G :=
  fullSmallEtaleExtendNativeBaseSheafFiberIso_inv_marked_naturality Y ξ f ζ h G

-- The canonical counit retains both original arrows in the marked naturality square.
example [IsAffine Y.left] {X : SmoothSite S} [IsAffine X.left]
    (f : X ⟶ Y) (ζ : Spec (.of Ω) ⟶ X.left) (h : ζ ≫ f.left = ξ)
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).inv.app
        ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F) ≫
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
        ((fullSmallEtaleAdjunction (SmoothSite.base S)).counit.app F).hom ≫
      SmoothSite.etaleNeighborhoodValuePullback f h F.obj =
    eqToHom (congrArg (fun z ↦ (pointSmallEtale z).sheafFiber.obj
        ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F))
        (SmoothSite.markedSmooth_baseMarking_eq Y ξ f ζ h).symm) ≫
      (fullSmallEtaleExtendNativeBaseSheafFiberIso X ζ).inv.app
        ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F) ≫
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} X ζ).presheafFiber.map
        ((fullSmallEtaleAdjunction (SmoothSite.base S)).counit.app F).hom :=
  fullSmallEtale_counit_nativeBase_marked_naturality Y ξ f ζ h F

-- The marked-map theorem consumes the actual native relative Frobenius and its actual twist.
example [IsAffine Y.left] (p : ℕ) [Fact p.Prime]
    (hS : Stacks.Frobenius.IsInCharacteristic S p)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let T := SmoothSite.frobeniusTwist p hS Y
    let f := SmoothSite.relativeFrobenius p hS Y
    let η := ξ ≫ f.left
    letI : IsAffine T.left := by
      change IsAffine (pullback Y.hom (Stacks.Frobenius.absoluteFrobenius S p hS))
      exact Pullback.isAffine_of_isAffine_isAffine_isAffine
        (X := Y.left) (Y := S) (Z := S) Y.hom
        (Stacks.Frobenius.absoluteFrobenius S p hS)
    (fullSmallEtaleExtendNativeBaseSheafFiberIso T η).inv.app G ≫
      SmoothSite.etaleNeighborhoodValuePullback f rfl
        ((fullSmallEtaleExtend (SmoothSite.base S)).obj G).obj =
    eqToHom (congrArg (fun z ↦ (pointSmallEtale z).sheafFiber.obj G)
        (SmoothSite.markedSmooth_baseMarking_eq T η f ξ rfl).symm) ≫
      (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).inv.app G := by
  dsimp only
  let : IsAffine (SmoothSite.frobeniusTwist p hS Y).left :=
    Pullback.isAffine_of_isAffine_isAffine_isAffine
      (X := Y.left) (Y := S) (Z := S) Y.hom
      (Stacks.Frobenius.absoluteFrobenius S p hS)
  exact fullSmallEtaleExtendNativeBaseSheafFiberIso_inv_marked_naturality _ _ _ _ rfl G

-- An original PST over the arbitrary original field enters only through its ordinary
-- graph restriction and sheafification; there is no PST over a replacement residue field.
example (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] (x : X.left)
    (p : X ⟶ SmoothSite.base (Spec (.of k)))
    (h : (GeometricPoint.ofPoint X.left x).hom ≫ p.left =
      (GeometricPoint.ofPoint X.left x).hom ≫ X.hom) :
    let F := (presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((PresheafWithTransfers.toPresheaf k).obj P)
    IsIso ((SmoothSite.etaleNeighborhoodPoint.{u, u + 1} X
      (GeometricPoint.ofPoint X.left x).hom).presheafFiber.map
        ((fullSmallEtaleAdjunction (SmoothSite.base (Spec (.of k)))).counit.app F).hom) ↔
    IsIso (SmoothSite.etaleNeighborhoodValuePullback p h
      ((PresheafWithTransfers.toPresheaf k).obj P)) :=
  isIso_fullSmallEtale_sheafification_counit_iff_structuralNeighborhoodPullback X
    (GeometricPoint.ofPoint X.left x).hom p h _

#print axioms GrothendieckTopology.Point.skyscraperSheafAdjunction_unit_app_π
#print axioms GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom
#print axioms SmoothSite.etaleNeighborhoodValuePullback_naturality
#print axioms SmoothSite.etaleNeighborhoodSheafificationIso_hom_pullback
#print axioms comapGerm_fullSmallEtaleExtendBaseSheafFiberIso_hom
#print axioms unit_germ_fullSmallEtaleExtendBaseSheafFiberIso_hom
#print axioms SmoothSite.toPresheafFiber_fiberMk
#print axioms nativeBaseGerm_fullSmallEtaleExtendNativeBaseSheafFiberIso_inv
#print axioms etaleUnit_fullSmallCounit
#print axioms nativeBaseGerm_fullSmallEtale_counit
#print axioms fullSmallEtale_counit_eq_structuralNeighborhoodPullback
#print axioms isIso_fullSmallEtale_counit_iff_structuralNeighborhoodPullback
#print axioms fullSmallEtale_counit_sheafification_eq_structuralNeighborhoodPullback
#print axioms isIso_fullSmallEtale_sheafification_counit_iff_structuralNeighborhoodPullback
#print axioms nativeBaseStalk_hom_ext
#print axioms nativeBaseGerm_transport
#print axioms SmoothSite.markedSmooth_baseMarking_eq
#print axioms fullSmallEtaleExtendNativeBaseSheafFiberIso_inv_marked_naturality
#print axioms fullSmallEtale_counit_nativeBase_marked_naturality
