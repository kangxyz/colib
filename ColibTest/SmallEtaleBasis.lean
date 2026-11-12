/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.Topology

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

noncomputable section

variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)

example : Sheaf (EtaleSeparatedFiniteType.etaleTopology X.left) AddCommGrpCat.{u + 1} ≌
    Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  EtaleSeparatedFiniteType.sheafEquivSmallEtale X

example (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((EtaleSeparatedFiniteType.sheafEquivSmallEtale X).inverse.obj F).obj =
      (EtaleSeparatedFiniteType.toSmallEtale X.left).op ⋙ F.obj := rfl

example {F G : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    ((EtaleSeparatedFiniteType.sheafEquivSmallEtale X).inverse.map f).hom =
      Functor.whiskerLeft (EtaleSeparatedFiniteType.toSmallEtale X.left).op f.hom := rfl

#print axioms EtaleSeparatedFiniteType.toSmallEtale_isCoverDense
#print axioms EtaleSeparatedFiniteType.sheafEquivSmallEtale
