/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Duality.Basic
public import Colib.CategoryTheory.Waldhausen.Approximation.Basic

/-! # Dual approximation on literal incoming arrows

Strict incoming factorization is ordinary App2 for the actual opposite functor.
The weak class of a compatible dual is precisely the opposite weak class, so
saturation transfers without any K-theoretic assumption.

Implementation provenance: `Quillen/Waldhausen/Approximation/Dual.lean:29-70`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen

/-- Dual App1/App2, with the actual incoming arrow and strict original equation. -/
@[colib_tag "COL-0308",
  colib_ref "quillen" "Quillen/Waldhausen/Approximation/Dual.lean:27-34" "adaptation"
    "Strict incoming App1/App2 on the original functor"]
structure HasDualApproximationProperty {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (W : Structure C) (V : Structure D)
    (fib : MorphismProperty C) (F : C ⥤ D) : Prop where
  /-- The original functor reflects weak equivalences. -/
  reflects {A B : C} (f : A ⟶ B) : V.weq (F.map f) → W.weq f
  /-- Every incoming arrow has a strict factorization through an admissible source map. -/
  lift {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    ∃ (X' : C) (i : X' ⟶ X) (p : Y ⟶ F.obj X'),
      fib i ∧ V.weq p ∧ p ≫ F.map i = f

section General
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {Wd : Structure Cᵒᵖ} {V : Structure D} {Vd : Structure Dᵒᵖ}
  (hW : IsCompatibleDual W Wd) (hV : IsCompatibleDual V Vd) {F : C ⥤ D}

namespace IsCompatibleDual
include hW

/-- The opposite weak class is exactly reversal of the original weak class. -/
theorem weq_eq_op : Wd.weq = W.weq.op := by
  funext A B f
  exact propext (hW.weak f.unop).symm

/-- Original saturation also holds in the literal dual weak class. -/
theorem dual_saturated [W.weq.HasTwoOutOfThreeProperty] :
    Wd.weq.HasTwoOutOfThreeProperty := by
  rw [weq_eq_op hW]
  infer_instance

end IsCompatibleDual

namespace HasDualApproximationProperty
variable (h : HasDualApproximationProperty W V Wd.cof.unop F)
include h hW hV

/-- Strict incoming factorization is actual App2 for the opposite functor. -/
theorem op : HasApproximationProperty Wd Vd F.op where
  reflects f hf := (hW.weak f.unop).mp (h.reflects f.unop ((hV.weak _).mpr hf))
  lift {X Y} f := by
    obtain ⟨X', i, p, hi, hp, eq⟩ := h.lift f.unop
    exact ⟨Opposite.op X', i.op, p.op, hi, (hV.weak _).mp hp,
      congrArg Quiver.Hom.op eq⟩

end HasDualApproximationProperty

end General

end CategoryTheory.Waldhausen
