/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Basic
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Ordinary global units on the smooth site

These are the actual units of scheme global sections with ordinary pullback.
Additive notation and universe lifting change neither elements nor restriction
maps. No transfers or sheaf condition are asserted in this lower definition.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The actual unit group of a commutative ring, in additive notation. -/
def ringUnitsFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙ CommGrpCat.toAddCommGrp

/-- Actual global units with every ordinary smooth-site restriction. -/
def unitsPresheaf (S : Scheme.{u}) : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (forgetScheme S).op ⋙ Scheme.Γ ⋙ ringUnitsFunctor

/-- The original large coefficient universe for ordinary global units. -/
def largeUnitsPresheaf (S : Scheme.{u}) : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  unitsPresheaf S ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The actual restriction is ordinary pullback of the unit, with the same universe lift. -/
@[simp] theorem largeUnitsPresheaf_map_apply {S : Scheme.{u}} {X Y : SmoothSite S}
    (f : X ⟶ Y) (v : (Γ(Y.left, ⊤))ˣ) :
    (largeUnitsPresheaf S).map f.op (ULift.up (Additive.ofMul v)) =
      ULift.up (Additive.ofMul (Units.map f.left.appTop.hom.toMonoidHom v)) := rfl

end AlgebraicGeometry.Scheme.SmoothSite
