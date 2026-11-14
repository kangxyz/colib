/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateSection
public import Colib.AlgebraicGeometry.KTheory.PerfectVectorBundleTensor
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic

/-! # The coordinate morphism on the original perfect coefficient complexes -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

variable (S : Scheme.{u})
local instance : MonoidalCategory (projectiveSpaceOver 1 S).Modules :=
  SheafOfModules.monoidalCategorySheafTensor (projectiveSpaceOver 1 S).sheaf

local notation "PL" => projectiveSpaceOver 1 S
local instance : MonoidalPreadditive (PL).Modules := by
  let := Abelian.hasFiniteBiproducts (C := (PL).Modules)
  exact SheafOfModules.monoidalPreadditiveSheafTensor (PL).sheaf

local instance :
    SheafOfModules.IsFiniteLocallyFree (R := (PL).ringCatSheaf) (twistOver 1 S (-1)) :=
  let : SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := (PL).ringCatSheaf) (twistOver 1 S (-1)) 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme PL _
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

/-- Applying multiplication by the original homogeneous coordinate termwise gives an actual
natural transformation of the native perfect complexes, without changing models. -/
def perfectNegativeTwistCoordinate (i : Fin 2) :
    Modules.perfectTensorRight (twistOver 1 S (-1)) ⟶
      𝟭 (ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := (projectiveSpaceOver 1 S).toRingedSpace))) where
  app K := ObjectProperty.homMk
    (((negativeTwistCoordinateNat S i).mapHomologicalComplex (.up ℤ)).app K.obj)
  naturality {K L} g := by
    apply ObjectProperty.hom_ext
    exact ((negativeTwistCoordinateNat S i).mapHomologicalComplex (.up ℤ)).naturality g.hom

end AlgebraicGeometry.Scheme.ProjectiveLine
