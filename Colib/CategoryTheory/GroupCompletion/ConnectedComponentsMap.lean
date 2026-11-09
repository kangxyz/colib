/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.ConnectedComponents
public import Colib.CategoryTheory.GroupCompletion.MonoidalFunctor

/-! # Strong monoidal functors on the actual completion component groups -/

@[expose] public noncomputable section

universe u v w z
open CategoryTheory MonoidalCategory
namespace CategoryTheory.GroupCompletion

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  {D : Type w} [Category.{z} D] [MonoidalCategory D] [SymmetricCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- The original two-coordinate functor induces an additive map of actual component groups. -/
def monoidalMapComponents : Localization.Components C →+ Localization.Components D where
  toFun := (monoidalMap F).mapConnectedComponents
  map_zero' := Localization.componentClass_iso
    ((ActionLocalization.ofFunctor (C := D)).mapIso
      ((Functor.Monoidal.εIso F).symm.prod (Functor.Monoidal.εIso F).symm))
  map_add' x y := by
    induction x using Quotient.inductionOn with
    | h X =>
      induction y using Quotient.inductionOn with
      | h Y =>
        exact Localization.componentClass_iso
          ((ActionLocalization.ofFunctor (C := D)).mapIso
            ((Functor.Monoidal.μIso F X.obj.1 Y.obj.1).symm.prod
              (Functor.Monoidal.μIso F X.obj.2 Y.obj.2).symm))

/-- No replacement of the original categorical component map is made. -/
theorem monoidalMapComponents_apply (x : Localization.Components C) :
    monoidalMapComponents F x = (monoidalMap F).mapConnectedComponents x := rfl

/-- The actual unit comparison identifies the images of original input generators. -/
@[simp] theorem monoidalMapComponents_unitClass (P : C) :
    monoidalMapComponents F (Localization.componentUnitClass P) =
      Localization.componentUnitClass (F.obj P) :=
  Localization.componentClass_iso ((monoidalMapUnitIso F).app P)

end CategoryTheory.GroupCompletion
