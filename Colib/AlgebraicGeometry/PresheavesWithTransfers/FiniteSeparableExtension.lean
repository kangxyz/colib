/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.FiniteSeparableForget
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction

/-!
# Original coefficients over a finite separable extension

For P over k, P_L evaluates P on the unchanged scheme viewed over k.
Its transfer action is the proved signed forget-base correspondence action.
This leaf isolates the actual coefficient functor, values and transfer action.
Preservation of ordinary homotopy invariance requires the separate actual
cylinder comparison and is not asserted in this leaf.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} (L : Type u) [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

local notation "F" => SmoothSite.finiteSeparableForgetBase k L

/-- Original coefficients extended by finite separable forgetting, with universe unchanged. -/
def finiteSeparableExtension (P : PresheafWithTransfers.{v} k) : PresheafWithTransfers.{v} L :=
  AdditiveFunctor.of ((Cor.finiteSeparableForgetBase k L).op ⋙ P.obj)

/-- Values are literally the original values on the unchanged scheme over k. -/
@[simp]
theorem finiteSeparableExtension_sections (P : PresheafWithTransfers.{v} k) (X : Cor L) :
    sections (finiteSeparableExtension L P) X =
      sections P ((Cor.finiteSeparableForgetBase k L).obj X) := rfl

/-- Every signed transfer is exactly the original coefficient action on its forgotten support. -/
@[simp]
theorem finiteSeparableExtension_transfer (P : PresheafWithTransfers.{v} k)
    {X Y : Cor L} (α : X ⟶ Y) :
    transfer (finiteSeparableExtension L P) α =
      transfer P ((Cor.finiteSeparableForgetBase k L).map α) := rfl

/-- Ordinary restriction keeps the original graph, not a separately supplied map. -/
theorem finiteSeparableExtension_graph (P : PresheafWithTransfers.{v} k)
    {X Y : SmoothSite (Spec (.of L))} (a : X ⟶ Y) :
    ((toPresheaf L).obj (finiteSeparableExtension L P)).map a.op =
      ((toPresheaf k).obj P).map ((F).map a).op := by
  change transfer P ((Cor.finiteSeparableForgetBase k L).map ((Cor.graphFunctor L).map a)) = _
  rw [Cor.finiteSeparableForgetBase_graph]
  rfl

end AlgebraicGeometry.PresheafWithTransfers
