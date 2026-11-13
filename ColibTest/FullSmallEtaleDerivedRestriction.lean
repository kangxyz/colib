/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.DerivedRestriction

/-! Independent derived universes and negative-degree full-small restriction. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE

universe u w w'

variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'}
  (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

example (V : EtaleSeparatedFiniteType X.left)
    (K : CochainComplex (Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}) ℤ) :
    fullSmallDerivedHomMap X V K (-1) 0 = 0 :=
  map_zero _

example (V : EtaleSeparatedFiniteType X.left)
    {K L : CochainComplex (Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}) ℤ}
    (g : K ⟶ L)
    (f : (DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (SmoothSite.etaleTopology B)).obj ((toSmoothSite X).obj V)) ⟶
        (DerivedCategory.Q.obj K)⟦(-2 : ℤ)⟧) :
    fullSmallDerivedHomMap X V L (-2) (f ≫ (DerivedCategory.Q.map g)⟦(-2 : ℤ)⟧') =
      fullSmallDerivedHomMap X V K (-2) f ≫
        (DerivedCategory.Q.map
          (((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).map g))⟦(-2 : ℤ)⟧' :=
  fullSmallDerivedHomMap_coefficient X V g (-2) f
