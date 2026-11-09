/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.SheavesWithTransfers.Limits

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w w'

variable (k : Type u) [Field k]

example (J : Type w) [Category.{w'} J] [HasLimitsOfShape J AddCommGrpCat.{v}] :
    HasLimitsOfShape J (PresheafWithTransfers.{v} k) := inferInstance

example (J : Type w) [Category.{w'} J] [HasLimitsOfShape J AddCommGrpCat.{v}] :
    PreservesLimitsOfShape J (PresheafWithTransfers.toPresheaf.{v} k) := inferInstance

example (J : Type w) [Category.{w'} J] [HasLimitsOfShape J AddCommGrpCat.{v}] :
    (PresheafWithTransfers.IsNisnevichSheaf.{v} k).IsClosedUnderLimitsOfShape J :=
  inferInstance

example : HasBinaryBiproducts (SheafWithTransfers.{v} k) := inferInstance

example : HasZeroObject (SheafWithTransfers.{v} k) := inferInstance

example : HasFiniteProducts (SheafWithTransfers.{v} k) :=
  ⟨fun n => SheafWithTransfers.hasLimitsOfShape k (Discrete (Fin n))⟩
