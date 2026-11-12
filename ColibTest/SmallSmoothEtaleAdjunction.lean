/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.Adjunction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

universe u

noncomputable section

variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)

example : (toSmoothSite X).IsContinuous (etaleTopology X.left)
    (SmoothSite.etaleTopology B) := inferInstance

example : (toSmoothSite X).IsCocontinuous (etaleTopology X.left)
    (SmoothSite.etaleTopology B) := inferInstance

example : etaleExtend X ⊣ etaleRestrict X := etaleExtendRestrictAdjunction X

example : PreservesFiniteLimits (etaleRestrict X) := inferInstance

example : PreservesFiniteColimits (etaleRestrict X) := inferInstance

example (F : Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}) :
    ((etaleRestrict X).obj F).obj = (toSmoothSite X).op ⋙ F.obj := rfl

example {F G : Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    ((etaleRestrict X).map f).hom = Functor.whiskerLeft (toSmoothSite X).op f.hom := rfl

example (k : Type u) [Field k] :
    fullSmallEtaleExtend (SmoothSite.base (Spec (.of k))) ⊣
      fullSmallEtaleRestrict (SmoothSite.base (Spec (.of k))) :=
  fullSmallEtaleAdjunction _

example (k : Type u) [Field k]
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((fullSmallEtaleExtend (SmoothSite.base (Spec (.of k)))).obj F) =
      (etaleExtend (SmoothSite.base (Spec (.of k)))).obj
        ((sheafEquivSmallEtale (SmoothSite.base (Spec (.of k)))).inverse.obj F) := rfl

#print axioms toSmoothSite_etale_isContinuous
#print axioms toSmoothSite_etale_isCocontinuous
#print axioms etaleExtendRestrictAdjunction
#print axioms etaleConstructedAdjunction_unit_app_hom
#print axioms etaleConstructedAdjunction_counit_app_hom
#print axioms etaleExtendConstructionIso_unit_app
#print axioms etaleExtendConstructionIso_counit_app
#print axioms fullSmallEtaleAdjunction
#print axioms fullSmallEtaleAdjunction_unit_app
#print axioms fullSmallEtaleAdjunction_counit_app
