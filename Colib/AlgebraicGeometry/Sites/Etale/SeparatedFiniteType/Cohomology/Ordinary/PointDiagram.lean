/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Nisnevich
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-! # Original ordinary cohomology on the actual marked-base diagram -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Point/OrdinaryColimit.lean`, blob `584af116905fe4b2e5babf886dc5c1a3d4b0f572`.
Only the literal diagram is extracted. No derived-direct-image fiber
comparison or acyclicity statement is silently imported.
Source candidate only; no elaboration result is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.FreeYonedaUnivLE
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (b : T ⟶ S)
  (Φ : (nisnevichTopology S).Point.{u + 1})
  {F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}}
  [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]

/-- The original ordinary cohomology presheaf restricted along geometric pullback. -/
def ordinaryPointCohomologyDiagram (n : ℕ) : Φ.fiber.Elementsᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.Elements.π Φ.fiber).op ⋙ (baseChange b).op ⋙
    cohomologyPresheaf.{u + 1, u + 1} F n

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
