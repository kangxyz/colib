/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.ExtPresheaf
import Colib.AlgebraicGeometry.SheavesWithTransfers.EnoughInjectives

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

universe w u

variable (k : Type u) [Field k]

example (X : Cor k) (F : SheafWithTransfers.{u + 1} k) :
    ((SheafWithTransfers.transferRepresentable k).obj X ⟶ F) ≃+
      PresheafWithTransfers.sections F.obj X :=
  SheafWithTransfers.transferSectionsEquiv k X F

example [HasExt.{w} (SheafWithTransfers.{u + 1} k)]
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    (SheafWithTransfers.transferExtPresheaf k F n).Additive := inferInstance

example (F : SheafWithTransfers.{u + 1} k) (n : ℕ) : PresheafWithTransfers.{u + 1} k := by
  let : HasExt.{u + 1} (SheafWithTransfers.{u + 1} k) := hasExt_of_enoughInjectives _
  exact .of (SheafWithTransfers.transferExtPresheaf k F n)
