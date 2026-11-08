/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Kernels annihilate restriction of scalars

The action in Mathlib's actual `ModuleCat.restrictScalars` sends a scalar `a`
to the action of its image. Hence the ring-map kernel annihilates every
restricted module. This elementary interface avoids unfolding concrete module
carriers, such as scheme stalks, inside downstream scalar calculations.
-/

@[expose] public section

universe u v w

namespace ModuleCat

/-- The kernel of a ring map annihilates each module restricted along that map. -/
theorem ker_le_annihilator_restrictScalars {A : Type u} {B : Type v}
    [Ring A] [Ring B] (f : A →+* B) (N : ModuleCat.{w} B) :
    RingHom.ker f ≤ Module.annihilator A ((restrictScalars f).obj N) := by
  intro a ha
  apply Module.mem_annihilator.mpr
  change ∀ m : N, f a • m = 0
  intro m
  rw [RingHom.mem_ker.mp ha, zero_smul]

end ModuleCat
