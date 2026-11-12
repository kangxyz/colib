/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Nisnevich
public import Colib.CategoryTheory.Sites.Cohomology.RestrictionSource

/-!
Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/CohomologySource.lean`,
blob `c666abac28cddafcf8ee47ea74052e3d0c9fae75`.

 Actual ordinary cohomology sources for big-to-small Nisnevich restriction. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE

variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)

/-- The original left adjoint to literal big-to-small restriction. -/
def extend : Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1} ⥤
    Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1} :=
  (toSmoothSite X).sheafPullback _ _ _

/-- This is an actual adjunction, not an acyclicity hypothesis. -/
def extendRestrictAdjunction : extend X ⊣ restrict X AddCommGrpCat.{u + 1} :=
  (toSmoothSite X).sheafAdjunctionContinuous _ _ _

/-- Exact original free abelian sheaf sources under this adjunction. -/
def extendSourceIso (U : EtaleSeparatedFiniteType X.left) :
    (extend X).obj
      (((freeYoneda.{u + 1} (nisnevichTopology X.left)).obj U)) ≅
      ((freeYoneda.{u + 1} (SmoothSite.nisnevichTopology B)).obj ((toSmoothSite X).obj U)) :=
  restrictionSourceIso.{u + 1, u, u + 1, u + 1} _ _ (toSmoothSite X) U

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
