/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardPerfectCoordinatePullback
public import Colib.AlgebraicGeometry.KTheory.PerfectVectorBundleTensorExact
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedTransformationCone

/-! # The supported cone of the original homogeneous coordinate -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

variable (S : Scheme.{u})

local notation "PL" => projectiveSpaceOver 1 S
set_option quotPrecheck false in
local notation "W" => RingedSpace.perfectComplexesWaldhausen (PL).toRingedSpace

local instance :
    SheafOfModules.IsFiniteLocallyFree (R := (PL).ringCatSheaf) (twistOver 1 S (-1)) :=
  let : SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := (PL).ringCatSheaf) (twistOver 1 S (-1)) 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme PL _
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

/-- The actual coordinate cone is exact into the native category supported off its standard open. -/
theorem perfectNegativeTwistCoordinateCone_exact (i : Fin 2) :
    IsExact (W).cof (W).weq
      (Modules.perfectSupportedWaldhausen (standardChart S i).ι).cof
      (Modules.perfectSupportedWaldhausen (standardChart S i).ι).weq
      (Modules.perfectSupportedTransformationCone (standardChart S i).ι
        (perfectNegativeTwistCoordinate S i) (perfectNegativeTwistCoordinate_openWeak S i)) := by
  let : (Modules.perfectTensorRight (twistOver 1 S (-1))).Additive :=
    Modules.perfectTensorRight_additive _
  apply Modules.perfectSupportedTransformationCone_waldhausenExact
  · exact Modules.perfectTensorRight_shortExact _
  · intro A hA
    exact hA
  · intro A B f hf
    exact (Modules.perfectTensorRight_waldhausenExact (twistOver 1 S (-1))).weak f hf
  · intro A B f hf
    exact hf

end AlgebraicGeometry.Scheme.ProjectiveLine
