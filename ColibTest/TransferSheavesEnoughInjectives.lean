/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.SheavesWithTransfers.EnoughInjectives

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

variable (k : Type u) [Field k]

example : Reflective (SheafWithTransfers.forget.{u + 1} k) := inferInstance

example : AB5OfSize.{u + 1, u + 1} (SheafWithTransfers.{u + 1} k) := inferInstance

example : HasSeparator (SheafWithTransfers.{u + 1} k) := inferInstance

example : IsGrothendieckAbelian.{u + 1} (SheafWithTransfers.{u + 1} k) := inferInstance

example : EnoughInjectives (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.enoughInjectives k
