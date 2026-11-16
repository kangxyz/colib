/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.CoefficientFunctors
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BoundedBelowTensor
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic

/-! # Geometric coefficient functors for the projective line

The first coordinate is actual direct image on flasque representatives. The second is
right tensor by `𝒪(-1)` followed by the actual Godement resolution and direct image.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Perf" => ObjectProperty.FullSubcategory (IsPerfectComplex (X :=
  LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X)))
local instance : IsProper π := isProper_projectiveSpaceOver 1 X

local instance :
    SheafOfModules.IsFiniteLocallyFree (R := (P).ringCatSheaf) (twistOver 1 X (-1)) :=
  let : SheafOfModules.IsFiniteLocallyFreeOfRank (R := (P).ringCatSheaf) (twistOver 1 X (-1)) 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme P _
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

/-- The untwisted coefficient functor is literal direct image. -/
def projectiveLineG₀ : Obj P ⥤ Perf :=
  perfectPushforward π

/-- The twisted coefficient functor uses right tensor and its actual Godement replacement. -/
def projectiveLineG₁ : Obj P ⥤ Perf :=
  ((inclusion P ⋙ BoundedBelowPerfect.tensorVectorBundleRight (twistOver 1 X (-1))) ⋙
    total P) ⋙ projectiveLineG₀ X

theorem projectiveLineG₀_exact :
    Waldhausen.IsExact (waldhausen P).cof (waldhausen P).weq
      (perfectComplexesWaldhausen X.toRingedSpace).cof
      (perfectComplexesWaldhausen X.toRingedSpace).weq (projectiveLineG₀ X) :=
  perfectPushforward_exact π

theorem projectiveLineG₁_exact :
    Waldhausen.IsExact (waldhausen P).cof (waldhausen P).weq
      (perfectComplexesWaldhausen X.toRingedSpace).cof
      (perfectComplexesWaldhausen X.toRingedSpace).weq (projectiveLineG₁ X) :=
  (((inclusion_exact P).comp
    (BoundedBelowPerfect.tensorVectorBundleRight_exact (twistOver 1 X (-1)))).comp
    (total_exact P)).comp (projectiveLineG₀_exact X)

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
