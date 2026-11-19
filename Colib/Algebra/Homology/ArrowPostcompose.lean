/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Postcomposition of arrows with an explicit endpoint equality

This lower interface is reconstructed from the requirements of the recovered
composition and certified-pair modules; it is not an exact historical recovery.
-/

@[expose] public noncomputable section

open CategoryTheory

variable {C : Type*} [Category C]

/-- Compose two complete arrows using their specified endpoint identification. -/
def arrowPostcompose (a b : Arrow C) (h : a.right = b.left) : Arrow C :=
  Arrow.mk (a.hom ≫ eqToHom h ≫ b.hom)

/-- Replacing an equal first arrow preserves the composite arrow. -/
theorem arrowPostcompose_congr_left {a a' : Arrow C} (e : a = a')
    (b : Arrow C) (h : a.right = b.left) (h' : a'.right = b.left) :
    arrowPostcompose a b h = arrowPostcompose a' b h' := by
  subst a'
  rfl
