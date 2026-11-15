/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.Sites.SheafifyContinuousMate
public import StacksFrontier.CategoryTheory.Sites.SheafPushforwardMonoidal
/-! # The canonical sheafification-reindex comparison is monoidal, not an isomorphism -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace CategoryTheory.Functor
open Stacks.SheafPushforwardMonoidal
attribute [local instance] Sheaf.monoidalCategory sheafToPresheafLaxMonoidal
  pushforwardLaxMonoidal
variable {C D : Type*} [Category C] [Category D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] (A : Type*) [Category A] [MonoidalCategory A]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal]

/-- The monoidal adjunction mate using the original unit and transported native
pushforward lax structure. It has the same direction as the canonical comparison. -/
def sheafifyReindexMonoidalMate :
    (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙ presheafToSheaf J A ⟶
      presheafToSheaf K A ⋙ F.sheafPushforwardContinuous A J K :=
  (Functor.leftUnitor ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙
    presheafToSheaf J A)).inv ≫
  Functor.whiskerRight (sheafificationAdjunction K A).unit
    ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙ presheafToSheaf J A) ≫
  (Functor.associator (presheafToSheaf K A) (sheafToPresheaf K A)
    ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙ presheafToSheaf J A)).hom ≫
  Functor.whiskerLeft (presheafToSheaf K A) (pushforwardIso J K A F).hom

/-- The mate is monoidal for exactly the original continuous pushforward lax structure. -/
instance sheafifyReindexMonoidalMate_isMonoidal :
    NatTrans.IsMonoidal (F.sheafifyReindexMonoidalMate J K A) := by
  have : NatTrans.IsMonoidal (pushforwardIso J K A F).hom :=
    Functor.LaxMonoidal.isMonoidal_transport_hom (pushforwardIso J K A F)
  dsimp only [sheafifyReindexMonoidalMate]
  infer_instance

omit [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal] in
/-- The mate is the original canonical comparison, not a new replacement. -/
theorem sheafifyReindexComparison_eq_monoidalMate :
    F.sheafifyReindexComparison J K A = F.sheafifyReindexMonoidalMate J K A := by
  apply NatTrans.ext
  funext P
  simpa only [sheafifyReindexMonoidalMate, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.comp_map, Category.id_comp, Category.comp_id,
    pushforwardIso_hom_app] using
      F.sheafifyReindexComparison_app_eq_map_comp_counit J K A P

/-- The canonical comparison respects both tensorators and units. It need not be invertible. -/
instance sheafifyReindexComparison_isMonoidal :
    NatTrans.IsMonoidal (F.sheafifyReindexComparison J K A) := by
  rw [F.sheafifyReindexComparison_eq_monoidalMate J K A]
  infer_instance

end CategoryTheory.Functor
