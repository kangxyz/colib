/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompPasting

/-! The actual total and whiskered routes have their complete native levels. -/
open CategoryTheory AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

example {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    HEq ((boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).level n)
      ((boundedAboveFlatAffineEvaluationCompModelDirectHomotopy f g).level n) :=
  boundedAboveFlatAffineEvaluationCompDirectHomotopy_level_heq f g n

example {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    HEq ((boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).level 0)
      ((boundedAboveFlatAffineEvaluationCompModelDirectHomotopy f g).level 0) :=
  boundedAboveFlatAffineEvaluationCompDirectHomotopy_level_heq f g 0

example {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    HEq ((boundedAboveFlatAffineEvaluationCompIteratedHomotopy f g).level n)
      ((boundedAboveFlatAffineEvaluationCompModelIteratedHomotopy f g).level n) :=
  boundedAboveFlatAffineEvaluationCompIteratedHomotopy_level_heq f g n

example {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    HEq ((boundedAboveFlatAffineEvaluationCompIteratedHomotopy f g).level 0)
      ((boundedAboveFlatAffineEvaluationCompModelIteratedHomotopy f g).level 0) :=
  boundedAboveFlatAffineEvaluationCompIteratedHomotopy_level_heq f g 0
