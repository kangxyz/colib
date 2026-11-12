/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.BasePointComparison
import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.CounitNeighborhoods

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

universe u

noncomputable section

variable {S : Scheme.{u}} [IsAffine S] (Y : SmoothSite S)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ Y.left)

local instance : InitiallySmall.{u + 1} (SmoothSite.EtaleNeighborhood Y ξ) :=
  SmoothSite.etaleNeighborhoodInitiallySmall.{u, u + 1} Y ξ

-- The marking over S is exactly the original composite, and Y need not be affine.
example (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    SmoothSite.etaleNeighborhoodValue Y ξ
        ((fullSmallEtaleExtend (SmoothSite.base S)).obj G).obj ≅
      (pointSmallEtale (ξ ≫ Y.hom)).sheafFiber.obj G :=
  (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).app G

example {G H : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : G ⟶ H) :
    (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).sheafFiber.map
        ((fullSmallEtaleExtend (SmoothSite.base S)).map f) ≫
        (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).hom.app H =
      (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).hom.app G ≫
        (pointSmallEtale (ξ ≫ Y.hom)).sheafFiber.map f :=
  (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).hom.naturality f

example (U : EtaleSeparatedFiniteType S)
    (z : (pointSmallEtale (ξ ≫ Y.hom)).fiber.obj ((toSmallEtale S).obj U)) :
    ∃ (A : SmoothSite.EtaleNeighborhood Y ξ)
      (f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶
        (toSmoothSite (SmoothSite.base S)).obj U),
      etaleNeighborhoodMapLift Y ξ U A f = z :=
  exists_etaleNeighborhood_mapLift Y ξ U z

example (U : EtaleSeparatedFiniteType S) (A : SmoothSite.EtaleNeighborhood Y ξ)
    (f g : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶
      (toSmoothSite (SmoothSite.base S)).obj U)
    (h : etaleNeighborhoodMapLift Y ξ U A f = etaleNeighborhoodMapLift Y ξ U A g) :
    ∃ (B : SmoothSite.EtaleNeighborhood Y ξ) (q : B ⟶ A),
      (SmoothSite.etaleNeighborhoodToSmooth Y ξ).map q ≫ f =
        (SmoothSite.etaleNeighborhoodToSmooth Y ξ).map q ≫ g :=
  exists_etaleNeighborhood_refinement_eq_of_mapLift_eq Y ξ U A f g h

example (U : EtaleSeparatedFiniteType S) (A : SmoothSite.EtaleNeighborhood Y ξ)
    (f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶
      (toSmoothSite (SmoothSite.base S)).obj U) :
    (smoothNeighborhoodBasePointIso Y ξ).inv.hom.app U
        (GrothendieckTopology.Point.ofIsCofiltered.fiberMk.{u + 1} f) =
      ULift.up (etaleNeighborhoodMapLift Y ξ U A f) :=
  smoothNeighborhoodBasePointIso_inv_hom_app_fiberMk Y ξ U A f

example (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : S.Etale)
    (x : (pointSmallEtale (ξ ≫ Y.hom)).fiber.obj U) :
    (pointSmallEtale (ξ ≫ Y.hom)).toPresheafFiber U x G.obj ≫
        (nativeBaseGeometricStalkIso Y ξ G).hom =
      (baseGeometricPoint Y ξ).toPresheafFiber U (ULift.up x) G.obj :=
  toPresheafFiber_nativeBaseGeometricStalkIso_hom Y ξ G U x

-- This is the actual source of the canonical counit studied in COL-1099.
example (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    SmoothSite.etaleNeighborhoodValue Y ξ
        ((fullSmallEtaleExtend (SmoothSite.base S)).obj
          ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F)).obj ≅
      (pointSmallEtale (ξ ≫ Y.hom)).sheafFiber.obj
        ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F) :=
  (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).app _

-- The original residue-geometric marking works over every field, not only rational points.
example (k : Type u) [Field k] (Y : SmoothSite (Spec (.of k))) (y : Y.left)
    (G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    SmoothSite.etaleNeighborhoodValue Y (GeometricPoint.ofPoint Y.left y).hom
        ((fullSmallEtaleExtend (SmoothSite.base (Spec (.of k)))).obj G).obj ≅
      (pointSmallEtale ((GeometricPoint.ofPoint Y.left y).hom ≫ Y.hom)).sheafFiber.obj G :=
  (fullSmallEtaleExtendNativeBaseSheafFiberIso Y (GeometricPoint.ofPoint Y.left y).hom).app G

#print axioms exists_etaleNeighborhood_mapLift
#print axioms exists_etaleNeighborhood_refinement_eq_of_mapLift_eq
#print axioms etaleNeighborhoodGermToLift_bijective
#print axioms etaleNeighborhoodBaseFiberIso
#print axioms toSmoothSite_base_representablyFlat
#print axioms toSmallEtale_representablyFlat
#print axioms smoothNeighborhoodBasePointIso
#print axioms smoothNeighborhoodBasePointIso_inv_hom_app_fiberMk
#print axioms etaleExtendBaseSheafFiberIso
#print axioms fullSmallEtaleExtendNativeBaseSheafFiberIso
#print axioms toSmallEtalePullbackEquivIso_unit_app
#print axioms toSmallEtalePullbackEquivIso_counit_app
#print axioms nativeBaseGeometricStalkIso_naturality
