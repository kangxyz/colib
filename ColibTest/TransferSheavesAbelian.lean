/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.SheavesWithTransfers.Exactness

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w w'

variable (k : Type u) [Field k]

example : Abelian (PresheafWithTransfers.{v} k) := inferInstance

example (J : Type w) [Category.{w'} J] [HasColimitsOfShape J AddCommGrpCat.{v}] :
    PreservesColimitsOfShape J (PresheafWithTransfers.toPresheaf.{v} k) := inferInstance

example : PreservesFiniteLimits (SheafWithTransfers.toSheaf.{v} k) := inferInstance

example : PreservesFiniteLimits (PresheafWithTransfers.nisnevichSheafify k) :=
  inferInstance

example : Abelian (SheafWithTransfers.{u + 1} k) := inferInstance
