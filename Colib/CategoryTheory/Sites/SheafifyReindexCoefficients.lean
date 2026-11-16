/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.SheafifyContinuous
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # Coefficient compatibility of continuous sheafification comparison

The comparison is the native one-way sheafification/reindexing map. Changing
coefficients uses the existing sheafification comparison, not exactness of
continuous sheaf pushforward and not an inverse to reindexing comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoryTheory.Functor

variable {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
variable (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [F.IsContinuous J K] (G : A ⥤ B)
variable [HasWeakSheafify J A] [HasWeakSheafify J B]
  [HasWeakSheafify K A] [HasWeakSheafify K B]
  [J.HasSheafCompose G] [K.HasSheafCompose G]
  [J.PreservesSheafification G] [K.PreservesSheafification G]

/-- The native coefficient comparison commutes with continuous reindexing. -/
theorem sheafifyReindexComparison_coefficients (P : Dᵒᵖ ⥤ A) :
    (sheafifyComposeIso J G (F.op ⋙ P)).hom ≫
      whiskerRight ((F.sheafifyReindexComparison J K A).app P).hom G =
    ((F.sheafifyReindexComparison J K B).app (P ⋙ G)).hom ≫
      whiskerLeft F.op (sheafifyComposeIso K G P).hom := by
  apply sheafify_hom_ext J _ _
    (((F.sheafPushforwardContinuous B J K).obj
      ((sheafCompose K G).obj ((presheafToSheaf K A).obj P))).property)
  rw [← Category.assoc, sheafComposeIso_hom_fac, ← whiskerRight_comp]
  ext X
  have hA := NatTrans.congr_app
    (F.toSheafify_sheafifyReindexComparison J K A P) X
  have hB := NatTrans.congr_app
    (F.toSheafify_sheafifyReindexComparison J K B (P ⋙ G)) X
  have hG := NatTrans.congr_app (sheafComposeIso_hom_fac K G P) (F.op.obj X)
  simp only [NatTrans.comp_app] at hA hB hG ⊢
  change G.map ((toSheafify J (F.op ⋙ P)).app X ≫
      ((F.sheafifyReindexComparison J K A).app P).hom.app X) =
    (toSheafify J (F.op ⋙ (P ⋙ G))).app X ≫
      ((F.sheafifyReindexComparison J K B).app (P ⋙ G)).hom.app X ≫
        (sheafifyComposeIso K G P).hom.app (F.op.obj X)
  erw [hA, ← Category.assoc, hB]
  exact hG.symm

end CategoryTheory.Functor
