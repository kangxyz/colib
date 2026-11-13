/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RepresentableLarge

/-!
# Additive Yoneda in the coefficient universe

Evaluation at the lifted full diagonal identifies morphisms from the existing
large representable with sections. Precomposition is the actual transfer.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- A section defines a map from the large representable by the original transfers. -/
def sectionHomLarge (P : PresheafWithTransfers.{u + 1} k) (X : Cor k) (s : sections P X) :
    (representableLarge k).obj X ⟶ P :=
  ObjectProperty.homMk
    { app Y := by
        change AddCommGrpCat.of (ULift.{u + 1} (Y.unop ⟶ X)) ⟶ sections P Y.unop
        exact AddCommGrpCat.ofHom
          { toFun a := transfer P a.down s
            map_zero' := by
              change transfer P (0 : Y.unop ⟶ X) s = 0
              rw [transfer_zero]
              rfl
            map_add' a b := by
              change transfer P (a.down + b.down) s = transfer P a.down s + transfer P b.down s
              rw [transfer_add]
              rfl }
      naturality Y Z f := by
        apply AddCommGrpCat.ext
        intro a
        change ULift.{u + 1} (Y.unop ⟶ X) at a
        change transfer P (f.unop ≫ a.down) s = transfer P f.unop (transfer P a.down s)
        rw [transfer_comp]
        rfl }

/-- Additive Yoneda with the actual universe-lifted signed correspondences. -/
def yonedaLargeAddEquiv (P : PresheafWithTransfers.{u + 1} k) (X : Cor k) :
    ((representableLarge k).obj X ⟶ P) ≃+ sections P X where
  toFun η := η.hom.app (op X) (ULift.up (𝟙 X))
  invFun := sectionHomLarge P X
  left_inv η := by
    apply ObjectProperty.hom_ext
    ext Y a
    change ULift.{u + 1} (Y.unop ⟶ X) at a
    change transfer P a.down (η.hom.app (op X) (ULift.up (𝟙 X))) = η.hom.app Y a
    have h := ConcreteCategory.congr_hom (η.hom.naturality a.down.op) (ULift.up (𝟙 X))
    change η.hom.app Y (ULift.up (a.down ≫ 𝟙 X)) =
      transfer P a.down (η.hom.app (op X) (ULift.up (𝟙 X))) at h
    have h' : transfer P a.down (η.hom.app (op X) (ULift.up (𝟙 X))) =
        η.hom.app Y (ULift.up a.down) := by
      simpa only [Category.comp_id] using h.symm
    exact h'.trans (congrArg (fun b : ULift.{u + 1} (Y.unop ⟶ X) => η.hom.app Y b)
      (ULift.up_down a))
  right_inv s := by
    change transfer P (𝟙 X) s = s
    rw [transfer_id]
    rfl
  map_add' _ _ := rfl

/-- The lifted Yoneda evaluation commutes with precomposition by a finite correspondence. -/
theorem yonedaLargeAddEquiv_naturality_left (P : PresheafWithTransfers.{u + 1} k)
    {X Y : Cor k} (α : X ⟶ Y) (η : (representableLarge k).obj Y ⟶ P) :
    yonedaLargeAddEquiv P X ((representableLarge k).map α ≫ η) =
      transfer P α (yonedaLargeAddEquiv P Y η) := by
  change η.hom.app (op X) (ULift.up (𝟙 X ≫ α)) =
    transfer P α (η.hom.app (op Y) (ULift.up (𝟙 Y)))
  have h := ConcreteCategory.congr_hom (η.hom.naturality α.op) (ULift.up (𝟙 Y))
  change η.hom.app (op X) (ULift.up (α ≫ 𝟙 Y)) =
    transfer P α (η.hom.app (op Y) (ULift.up (𝟙 Y))) at h
  rw [Category.id_comp]
  simpa only [Category.comp_id] using h

end AlgebraicGeometry.PresheafWithTransfers
