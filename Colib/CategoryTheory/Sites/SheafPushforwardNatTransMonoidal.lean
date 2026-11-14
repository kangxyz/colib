/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.CategoryTheory.Sites.SheafPushforwardMonoidal

/-! # Natural transformations of sites induce monoidal maps of sheaf pushforwards -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Functor.LaxMonoidal

set_option backward.isDefEq.respectTransparency false

namespace Colib.SheafPushforwardMonoidal

variable {C D : Type*} [Category* C] [Category* D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type*) [Category* A] [MonoidalCategory A]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory
  Stacks.SheafPushforwardMonoidal.sheafToPresheafLaxMonoidal
  Stacks.SheafPushforwardMonoidal.pushforwardLaxMonoidal

/-- Precomposition by a natural transformation is monoidal for the canonical sheaf
pushforward tensorators. -/
theorem pushforwardNatTrans_isMonoidal {F G : C ⥤ D}
    [F.IsContinuous J K] [G.IsContinuous J K] (α : F ⟶ G) :
    (Functor.sheafPushforwardContinuousNatTrans α A J K).IsMonoidal where
  unit := by
    apply Stacks.SheafPushforwardMonoidal.hom_ext_unit
    rw [Functor.map_comp, ← Category.assoc,
      Stacks.SheafPushforwardMonoidal.ε_sheafToPresheaf_comp_map_ε_pushforward,
      Stacks.SheafPushforwardMonoidal.ε_sheafToPresheaf_comp_map_ε_pushforward]
    ext U
    simpa using ((ε (sheafToPresheaf K A)).naturality ((α.app (unop U)).op)).symm
  tensor M N := by
    apply Stacks.SheafPushforwardMonoidal.hom_ext_tensor
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc,
      Stacks.SheafPushforwardMonoidal.μ_sheafToPresheaf_comp_map_μ_pushforward,
      ← Functor.LaxMonoidal.μ_natural_assoc,
      Stacks.SheafPushforwardMonoidal.μ_sheafToPresheaf_comp_map_μ_pushforward]
    ext U
    exact ((μ (sheafToPresheaf K A) M N).naturality ((α.app (unop U)).op)).symm

/-- The canonical identification of identity-site pushforward with the identity is monoidal. -/
theorem pushforwardId_isMonoidal :
    (Functor.sheafPushforwardContinuousId A J).hom.IsMonoidal where
  unit := by
    apply Stacks.SheafPushforwardMonoidal.hom_ext_unit
    dsimp [Functor.sheafPushforwardContinuousId]
    simp only [Category.comp_id]
    exact
      Stacks.SheafPushforwardMonoidal.ε_sheafToPresheaf_comp_map_ε_pushforward J J A (𝟭 C)
  tensor M N := by
    apply Stacks.SheafPushforwardMonoidal.hom_ext_tensor
    dsimp [Functor.sheafPushforwardContinuousId]
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight]
    change _ = μ (sheafToPresheaf J A) M N ≫ 𝟙 _
    rw [Category.comp_id]
    exact
      Stacks.SheafPushforwardMonoidal.μ_sheafToPresheaf_comp_map_μ_pushforward J J A (𝟭 C) M N

omit [MonoidalCategory A] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal] in
/-- The unit of the sheaf pushforward adjunction is induced by the site counit. -/
theorem sheafPushforwardAdjunction_unit_eq {F : C ⥤ D} {G : D ⥤ C}
    [F.IsContinuous J K] [G.IsContinuous K J] (adj : F ⊣ G) :
    let := Functor.isContinuous_comp G F K J K
    (adj.sheafPushforwardContinuous (E := A) J K).unit =
      (Functor.sheafPushforwardContinuousId A K).inv ≫
        Functor.sheafPushforwardContinuousNatTrans adj.counit A K K ≫
          (Functor.sheafPushforwardContinuousComp' (Iso.refl (G ⋙ F)) A K J K).inv := by
  let := Functor.isContinuous_comp G F K J K
  ext M U
  simp only [Functor.id_obj, Functor.comp_obj,
    Adjunction.sheafPushforwardContinuous_unit_app_hom_app,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom,
    ObjectProperty.ι_obj, Functor.sheafPushforwardContinuousId_inv_app_hom_app,
    Functor.whiskerRight_app,
    Functor.op_obj, op_unop, NatTrans.op_app,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app, Iso.refl_hom,
    NatTrans.id_app, op_id, CategoryTheory.Functor.map_id, Category.id_comp]
  change M.obj.map (adj.counit.app (unop U)).op =
    M.obj.map (adj.counit.app (unop U)).op ≫ 𝟙 _
  simp only [Category.comp_id]

/-- The original sheaf restriction adjunction unit is monoidal for the canonical lax
structures. The left functor need not first be promoted to strong monoidal. -/
theorem sheafPushforwardAdjunction_unit_isMonoidal {F : C ⥤ D} {G : D ⥤ C}
    [F.IsContinuous J K] [G.IsContinuous K J] (adj : F ⊣ G) :
    (adj.sheafPushforwardContinuous (E := A) J K).unit.IsMonoidal := by
  let := Functor.isContinuous_comp G F K J K
  have := pushforwardId_isMonoidal K A
  have := pushforwardNatTrans_isMonoidal K K A adj.counit
  rw [sheafPushforwardAdjunction_unit_eq J K A adj]
  infer_instance

end Colib.SheafPushforwardMonoidal
