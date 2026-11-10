/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Chow.FiniteFlatBaseChange

noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

example (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsFinite f] (hf : f ≫ sY = sX)
    (n : ℤ) (α : CycleGroup C sX n) (y : Y) :
    (properPushforward C sX sY f hf n α).val y =
      ∑ᶠ x ∈ f.base ⁻¹' {y}, α.val x * (f.residueDegree x : ℤ) := by
  rw [properPushforward_val_eq_finiteCyclePushforward, finiteCyclePushforward_apply]

example (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsFinite f] (hf : f ≫ sY = sX)
    (n : ℤ) (α : CycleGroup C sX n) :
    (properPushforward C sX sY f hf n (-α)).val =
      -finiteCyclePushforward f α.val := by
  rw [properPushforward_val_eq_finiteCyclePushforward]
  exact map_neg _ _

#check finiteCyclePushforward_flatPullback
#check finite_flatBaseChange_fixedLabel
