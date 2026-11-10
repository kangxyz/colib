/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Representable

/-!
# Universe-lifted signed representables

Extracted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Presheaf/ReducedTorus.lean`, blob
`fff7335f6136869c80502d756b6a9990b17f0f90`.
Uses native signed cycles and the actual sheafification maps.
No ordinary derived cohomology comparison is claimed.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

private instance ulift_additive : AddCommGrpCat.uliftFunctor.{u + 1, u}.Additive where
  map_add := by intros; ext x; rfl

/-- The genuine signed-correspondence representable, raised to the coefficient
universe needed by sheafification on the actual smooth site. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Presheaf/ReducedTorus.lean:41-48"
  "adaptation" "Universe lift of actual signed finite-correspondence groups"]
def representableLarge : Cor k ⥤ PresheafWithTransfers.{u + 1} k :=
  (additiveFunctor _ _).lift
    (representable k ⋙ forget ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{u + 1, u})
    (fun X => by
      change (((representable k).obj X).obj ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).Additive
      infer_instance)

/-- Sections are precisely universe lifts of actual signed finite cycles. -/
@[simp]
theorem representableLarge_sections (X Y : Cor k) :
    sections ((representableLarge k).obj X) Y =
      AddCommGrpCat.of (ULift.{u + 1} (Y ⟶ X)) := rfl

/-- Every signed transfer remains literal precomposition of actual cycles. -/
@[simp↓]
theorem representableLarge_transfer_apply {X Y Z : Cor k}
    (α : Y ⟶ Z) (β : Z ⟶ X) :
    transfer ((representableLarge k).obj X) α (ULift.up β) =
      ULift.up (α ≫ β) := rfl

/-- Maps of representing objects remain literal postcomposition of cycles. -/
@[simp↓]
theorem representableLarge_map_app_apply {X Y Z : Cor k}
    (α : X ⟶ Y) (β : Z ⟶ X) :
    ((representableLarge k).map α).hom.app (op Z) (ULift.up β) =
      ULift.up (β ≫ α) := rfl

end AlgebraicGeometry.PresheafWithTransfers
