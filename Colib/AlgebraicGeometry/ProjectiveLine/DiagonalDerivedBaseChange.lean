/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalSequence
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.GlobalBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfect
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension

/-! # Derived base change along the two projections of the projective line

The self-square of the relative projective line carries the canonical derived
base-change mate. The proper flat perfect pushforward theorem makes it
invertible on the full subcategory of perfect derived objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange

namespace AlgebraicGeometry.Scheme

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "p₁" => pullback.fst π π
local notation "p₂" => pullback.snd π π

/-- The self-square with the second projection as the coefficient pullback. -/
theorem projectiveLineDiagonal_isPullback : IsPullback p₂ p₁ π π :=
  (IsPullback.of_hasPullback π π).flip

/-- The canonical self-base-change mate is an isomorphism on each perfect
coefficient, by the proper flat pushforward theorem [Stacks, Tag 0B91]. -/
theorem projectiveLineDiagonalDerivedBaseChangeMap_isIso
    (E : DerivedCategory (P).Modules) (hE : IsPerfect (X := (P).toRingedSpace) E) :
    IsIso (derivedBaseChangeMap (p₂).toLRSHom.toShHom (p₁).toLRSHom.toShHom
      (π).toLRSHom.toShHom (π).toLRSHom.toShHom
      (comp_toShHom_of_comm (projectiveLineDiagonal_isPullback X).w) E) := by
  let := isProper_projectiveSpaceOver 1 X
  exact (isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat_of_isProper π E hE).2
    π p₁ p₂ (projectiveLineDiagonal_isPullback X)

end AlgebraicGeometry.Scheme
