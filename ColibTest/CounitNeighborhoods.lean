/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.CounitNeighborhoods

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

universe u

noncomputable section

variable {S : Scheme.{u}} [IsAffine S] (X Y : SmoothSite S)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ Y.left)
  (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1})

-- The actual native point is on the original smooth object Y, not on the base.
example :
    SmoothSite.etaleNeighborhoodValue Y ξ F.obj ≅
      (pointSmallEtale ξ).sheafFiber.obj ((fullSmallEtaleRestrict Y).obj F) :=
  fullSmallEtaleRestrictNeighborhoodIso Y ξ F

example : (affineNeighborhoodToSmallPoint Y ξ).Initial := inferInstance

-- Both the actual dense-basis equivalence and the actual sheafification unit are retained.
example :
    (fullSmallEtaleExtendNeighborhoodIso X Y ξ F).hom ≫
        (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
          (((toSmoothSite X).op.lanAdjunction AddCommGrpCat.{u + 1}).counit.app F.obj) =
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
        ((fullSmallEtaleAdjunction X).counit.app F).hom :=
  fullSmallEtaleExtendNeighborhoodIso_hom_counit X Y ξ F

-- This tests the original map, not an isomorphic replacement adjunction.
example (A : SmoothSite.EtaleNeighborhood Y ξ) (U : EtaleSeparatedFiniteType X.left)
    (f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶ (toSmoothSite X).obj U) :
    ((toSmoothSite X).op.lanUnit.app ((toSmoothSite X).op ⋙ F.obj)).app (op U) ≫
        (etaleRestrictLan X F).map f.op ≫
        SmoothSite.toEtaleNeighborhoodValue Y ξ A (etaleRestrictLan X F) ≫
        (fullSmallEtaleExtendNeighborhoodIso X Y ξ F).inv ≫
        (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
          ((fullSmallEtaleAdjunction X).counit.app F).hom =
      F.obj.map f.op ≫ SmoothSite.toEtaleNeighborhoodValue Y ξ A F.obj :=
  fullSmallEtale_counit_representative X Y ξ F A U f

example (A : SmoothSite.EtaleNeighborhood Y ξ) :
    SmoothSite.toEtaleNeighborhoodValue Y ξ A F.obj ≫
        (fullSmallEtaleRestrictNeighborhoodIso Y ξ F).hom =
      (((sheafEquivSmallEtale Y).unitIso.app ((etaleRestrict Y).obj F)).hom.hom.app
        (op ((affineEtaleToSeparatedFiniteType Y).obj A.obj))) ≫
        (pointSmallEtale ξ).toPresheafFiber ((AffineEtale.Spec Y.left).obj A.obj) A.val
          ((fullSmallEtaleRestrict Y).obj F).obj :=
  toEtaleNeighborhoodValue_fullSmallEtaleRestrictNeighborhoodIso_hom Y ξ F A

example {G : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map f.hom ≫
        (fullSmallEtaleRestrictNeighborhoodIso Y ξ G).hom =
      (fullSmallEtaleRestrictNeighborhoodIso Y ξ F).hom ≫
        (pointSmallEtale ξ).sheafFiber.map ((fullSmallEtaleRestrict Y).map f) :=
  fullSmallEtaleRestrictNeighborhoodIso_naturality Y ξ f

-- No algebraic-closedness or rationality assumption is imposed on the base field.
example (k : Type u) [Field k]
    (F : Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :
    IsIso ((fullSmallEtaleAdjunction (SmoothSite.base (Spec (.of k)))).counit.app F) ↔
      ∀ (Y : SmoothSite (Spec (.of k))) (y : Y.left), IsClosed ({y} : Set Y.left) →
        IsIso ((SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y
          (GeometricPoint.ofPoint Y.left y).hom).presheafFiber.map
            (((toSmoothSite (SmoothSite.base (Spec (.of k)))).op.lanAdjunction
              AddCommGrpCat.{u + 1}).counit.app F.obj)) :=
  isIso_fullSmallEtale_counit_iff_closedNeighborhood_restriction _ F

example (y : Y.left) :
    IsIso ((pointSmallEtale (GeometricPoint.ofPoint Y.left y).hom).sheafFiber.map
      ((fullSmallEtaleRestrict Y).map ((fullSmallEtaleAdjunction X).counit.app F))) ↔
    IsIso ((SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y
      (GeometricPoint.ofPoint Y.left y).hom).presheafFiber.map
        (((toSmoothSite X).op.lanAdjunction AddCommGrpCat.{u + 1}).counit.app F.obj)) :=
  isIso_fullSmallEtale_counit_smallStalk_iff X Y _ F

#print axioms etaleExtendNeighborhoodIso
#print axioms fullSmallEtaleExtendNeighborhoodIso
#print axioms toSheafify_etaleConstructedAdjunction_counit
#print axioms fullSmallEtaleExtendNeighborhoodIso_hom_counit
#print axioms fullSmallEtale_counit_representative
#print axioms isIso_fullSmallEtale_counit_iff_closedNeighborhood_restriction
#print axioms affineNeighborhoodToSmallPoint_initial
#print axioms fullSmallEtaleRestrictNeighborhoodIso
#print axioms toEtaleNeighborhoodValue_fullSmallEtaleRestrictNeighborhoodIso_hom
#print axioms fullSmallEtaleRestrictNeighborhoodIso_naturality
#print axioms isIso_fullSmallEtale_counit_smallStalk_iff
