/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoefficients

/-! The actual coefficient model arrow is its canonical exact chosen-zero normalization. -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original native arrow, including exactness and the chosen zero, is unchanged. -/
theorem boundedAboveFlatAffinePullbackModelMap_eq_asSmallCategoryMap
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatAffinePullbackModelMap f =
      asSmallCategoryMap
        (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
        (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace)
        (boundedAboveFlatPerfectPullback_isExact (Spec.map f)).rebase
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) := by
  rfl

end AlgebraicGeometry.Scheme.Modules
