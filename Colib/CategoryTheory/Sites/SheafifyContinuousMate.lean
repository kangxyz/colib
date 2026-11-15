/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.Sites.SheafifyContinuous
/-! # The original sheafification-reindex comparison as its adjunction mate -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] (A : Type*) [Category A]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The original canonical comparison is sheafification of the reindexed unit,
followed by the original counit. No invertibility is asserted. -/
theorem sheafifyReindexComparison_app_eq_map_comp_counit (P : Dᵒᵖ ⥤ A) :
    (F.sheafifyReindexComparison J K A).app P =
      (presheafToSheaf J A).map
        (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op).map (toSheafify K P)) ≫
      (sheafificationAdjunction J A).counit.app
        ((F.sheafPushforwardContinuous A J K).obj ((presheafToSheaf K A).obj P)) := by
  let X := ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op).obj P
  let Y := (F.sheafPushforwardContinuous A J K).obj ((presheafToSheaf K A).obj P)
  let φ : X ⟶ (sheafToPresheaf J A).obj Y :=
    ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op).map (toSheafify K P)
  let e := (sheafificationAdjunction J A).homEquiv X Y
  calc
    _ = e.symm φ := by
      apply e.injective
      exact (F.toSheafify_sheafifyReindexComparison J K A P).trans
        (e.apply_symm_apply φ).symm
    _ = _ := (sheafificationAdjunction J A).homEquiv_counit X Y φ

end CategoryTheory.Functor
