/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateScalarAction
public import Colib.AlgebraicGeometry.ProjectiveLine.StandardPerfectCoordinatePullback

/-! # The polynomial coordinate on the native restricted perfect complexes -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

set_option backward.isDefEq.respectTransparency false in
/-- The actual flat pullback of the coordinate map for `T₀` is the pulled-back map for
`T₁` followed by the actual polynomial scalar, degree by degree. -/
theorem perfectNegativeTwistCoordinate_pullback_zero (X : QuasiCompactSchemes.{u})
    (K : ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := (projectiveSpaceOver 1 X.obj).toRingedSpace))) :
    let U := negativeChart X.obj
    let F := Modules.perfectFlatPullback U.ι
    F.map ((perfectNegativeTwistCoordinate X.obj 0).app K) =
      F.map ((perfectNegativeTwistCoordinate X.obj 1).app K) ≫
        (Modules.perfectGlobalScalar U.toScheme (negativeChartCoordinate X)).app (F.obj K) := by
  apply ObjectProperty.hom_ext
  ext j : 1
  exact negativeTwistCoordinate_pullback_zero X (K.obj.X j)

set_option backward.isDefEq.respectTransparency false in
/-- The scalar identity also holds for the literal restriction used by localization. -/
theorem perfectNegativeTwistCoordinate_restrict_zero (X : QuasiCompactSchemes.{u})
    (K : ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := (projectiveSpaceOver 1 X.obj).toRingedSpace))) :
    let U := negativeChart X.obj
    let R := Modules.perfectComplexesRestrictOpenImmersion U.ι
    R.map ((perfectNegativeTwistCoordinate X.obj 0).app K) =
      R.map ((perfectNegativeTwistCoordinate X.obj 1).app K) ≫
        (Modules.perfectGlobalScalar U.toScheme (negativeChartCoordinate X)).app (R.obj K) := by
  let U := negativeChart X.obj
  let R := Modules.perfectComplexesRestrictOpenImmersion U.ι
  let E := Modules.perfectRestrictIsoFlatPullback U.ι
  let α := perfectNegativeTwistCoordinate X.obj
  let σ := Modules.perfectGlobalScalar U.toScheme (negativeChartCoordinate X)
  let b := E.hom.app K
  apply (cancel_mono b).mp
  change R.map ((α 0).app K) ≫ b =
    (R.map ((α 1).app K) ≫ σ.app (R.obj K)) ≫ b
  calc
    R.map ((α 0).app K) ≫ b =
        E.hom.app _ ≫ (Modules.perfectFlatPullback U.ι).map ((α 0).app K) :=
      (E.hom.naturality ((α 0).app K))
    _ = E.hom.app _ ≫ ((Modules.perfectFlatPullback U.ι).map ((α 1).app K) ≫
          σ.app ((Modules.perfectFlatPullback U.ι).obj K)) := by
      rw [perfectNegativeTwistCoordinate_pullback_zero]
    _ = R.map ((α 1).app K) ≫ b ≫
          σ.app ((Modules.perfectFlatPullback U.ι).obj K) := by
      rw [← Category.assoc, ← E.hom.naturality, Category.assoc]
      rfl
    _ = (R.map ((α 1).app K) ≫ σ.app (R.obj K)) ≫ b := by
      rw [Category.assoc]
      exact congrArg (fun c => R.map ((α 1).app K) ≫ c) (σ.naturality b)

end AlgebraicGeometry.Scheme.ProjectiveLine
