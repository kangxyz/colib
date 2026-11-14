/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Limits.PointedSmash
public import Colib.CategoryTheory.Sites.Simplicial.FreeAbelianProductTensor
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.AddCommGrpCatTransported
import StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryTensorColimits

/-!
# Reduced free abelianization of the smash product

The two actual pointed axes of the product become the two tensor relations
defining the tensor of reduced free abelianizations. The quotient legs give
a natural isomorphism of simplicial abelian presheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonoidalCategory

attribute [local instance] AddCommGrpCat.monoidalCategory
  AddCommGrpCat.monoidalClosed AddCommGrpCat.braidedCategory
  AddCommGrpCat.uliftIntEquivalenceInverseMonoidal

universe u v w

namespace CategoryTheory.PointedSimplicialPresheaf

private local instance : MonoidalPreadditive AddCommGrpCat.{w + 1} := by
  let F := (AddCommGrpCat.uliftIntEquivalence.{w + 1}).inverse
  let : F.Additive := F.additive_of_preserves_binary_products
  exact monoidalPreadditive_of_faithful F

variable {C : Type u} [Category.{v} C]

local notation "F" => freeAbelian C
local notation "R" => reducedFreeAbelian C

private abbrev leftAxis (X Y : PointedSimplicialPresheaf.{w + 1} C) : X.right ⟶ X.right ⨯ Y.right :=
  prod.lift (𝟙 X.right) (terminal.from X.right ≫ Y.hom)

private abbrev rightAxis (X Y : PointedSimplicialPresheaf.{w + 1} C) :
    Y.right ⟶ X.right ⨯ Y.right :=
  prod.lift (terminal.from Y.right ≫ X.hom) (𝟙 Y.right)

private theorem leftAxis_eq (X Y : PointedSimplicialPresheaf.{w + 1} C) :
    leftAxis X Y = (Limits.prod.rightUnitor X.right).inv ≫ prod.map (𝟙 X.right) Y.hom := by
  apply prod.hom_ext <;> simp [Limits.prod.rightUnitor]

private theorem rightAxis_eq (X Y : PointedSimplicialPresheaf.{w + 1} C) :
    rightAxis X Y = (Limits.prod.leftUnitor Y.right).inv ≫ prod.map X.hom (𝟙 Y.right) := by
  apply prod.hom_ext <;> simp [Limits.prod.leftUnitor]

private def freeAxesTensorIso (X Y : PointedSimplicialPresheaf.{w + 1} C) :
    (F).obj (X.right ⨿ Y.right) ≅
      ((F).obj X.right ⊗ (F).obj (⊤_ _)) ⨿ ((F).obj (⊤_ _) ⊗ (F).obj Y.right) :=
  (PreservesColimitPair.iso F X.right Y.right).symm ≪≫
    coprod.mapIso
      ((F).mapIso (Limits.prod.rightUnitor X.right).symm ≪≫
        freeAbelianProductTensorIso X.right (⊤_ _))
      ((F).mapIso (Limits.prod.leftUnitor Y.right).symm ≪≫
        freeAbelianProductTensorIso (⊤_ _) Y.right)

private theorem freeAxesTensorIso_hom (X Y : PointedSimplicialPresheaf.{w + 1} C) :
    (freeAxesTensorIso X Y).hom ≫
        coprod.desc ((F).obj X.right ◁ (F).map Y.hom)
          ((F).map X.hom ▷ (F).obj Y.right) =
      (F).map (Under.axesToProduct X Y) ≫
        (freeAbelianProductTensorIso X.right Y.right).hom := by
  let c := PreservesColimitPair.iso (F) X.right Y.right
  apply (cancel_epi c.hom).mp
  apply coprod.hom_ext
  · have h := freeAbelianProductTensorIso_naturality (𝟙 X.right) Y.hom
    simp only [Functor.map_id, MonoidalCategory.id_tensorHom] at h
    have ha : (coprod.inl : X.right ⟶ X.right ⨿ Y.right) ≫
        Under.axesToProduct X Y = leftAxis X Y := coprod.inl_desc _ _
    have hc : coprod.inl ≫ c.hom = (F).map (coprod.inl : X.right ⟶ X.right ⨿ Y.right) :=
      inl_coprodComparison _ _ _
    let e := freeAbelianProductTensorIso X.right Y.right
    let l := (F).mapIso (Limits.prod.rightUnitor X.right).symm ≪≫
      freeAbelianProductTensorIso X.right (⊤_ _)
    let r := (F).mapIso (Limits.prod.leftUnitor Y.right).symm ≪≫
      freeAbelianProductTensorIso (⊤_ _) Y.right
    change coprod.inl ≫ c.hom ≫ c.inv ≫ coprod.map l.hom r.hom ≫ _ =
      coprod.inl ≫ c.hom ≫ (F).map (Under.axesToProduct X Y) ≫ e.hom
    rw [Iso.hom_inv_id_assoc, coprod.inl_map_assoc, coprod.inl_desc, reassoc_of% hc,
      ← (F).map_comp_assoc, ha, leftAxis_eq, (F).map_comp, Category.assoc, h]
    simp only [l, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  · have h := freeAbelianProductTensorIso_naturality X.hom (𝟙 Y.right)
    simp only [Functor.map_id, MonoidalCategory.tensorHom_id] at h
    have ha : (coprod.inr : Y.right ⟶ X.right ⨿ Y.right) ≫
        Under.axesToProduct X Y = rightAxis X Y := coprod.inr_desc _ _
    have hc : coprod.inr ≫ c.hom = (F).map (coprod.inr : Y.right ⟶ X.right ⨿ Y.right) :=
      inr_coprodComparison _ _ _
    let e := freeAbelianProductTensorIso X.right Y.right
    let l := (F).mapIso (Limits.prod.rightUnitor X.right).symm ≪≫
      freeAbelianProductTensorIso X.right (⊤_ _)
    let r := (F).mapIso (Limits.prod.leftUnitor Y.right).symm ≪≫
      freeAbelianProductTensorIso (⊤_ _) Y.right
    change coprod.inr ≫ c.hom ≫ c.inv ≫ coprod.map l.hom r.hom ≫ _ =
      coprod.inr ≫ c.hom ≫ (F).map (Under.axesToProduct X Y) ≫ e.hom
    rw [Iso.hom_inv_id_assoc, coprod.inr_map_assoc, coprod.inr_desc, reassoc_of% hc,
      ← (F).map_comp_assoc, ha, rightAxis_eq, (F).map_comp, Category.assoc, h]
    simp only [r, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]

private theorem terminal_from_axes_epi (X Y : PointedSimplicialPresheaf.{w + 1} C) :
    Epi (terminal.from (X.right ⨿ Y.right) : X.right ⨿ Y.right ⟶ ⊤_ (Cᵒᵖ ⥤ SSet.{w + 1})) := by
  have h : (X.hom ≫ (coprod.inl : X.right ⟶ X.right ⨿ Y.right)) ≫ terminal.from _ = 𝟙 _ :=
    terminal.hom_ext _ _
  exact epi_of_epi_fac h

private abbrev smashReduction (X Y : PointedSimplicialPresheaf.{w + 1} C) :
    (F).obj (X.right ⨯ Y.right) ⟶ (R).obj (Under.smash X Y) :=
  (F).map (Under.toSmash X Y) ≫ reduction C (Under.smash X Y)

private theorem freeAxes_smashReduction (X Y : PointedSimplicialPresheaf.{w + 1} C) :
    (F).map (Under.axesToProduct X Y) ≫ smashReduction X Y = 0 := by
  rw [← Functor.map_comp_assoc, Under.axesToProduct_toSmash, Functor.map_comp,
    Category.assoc, basepoint_reduction, comp_zero]

private def smashReductionIsCokernel (X Y : PointedSimplicialPresheaf.{w + 1} C) :
    IsColimit (CokernelCofork.ofπ (smashReduction X Y) (freeAxes_smashReduction X Y)) := by
  let e := terminal.from (X.right ⨿ Y.right)
  let h := IsPushout.of_hasPushout (Under.axesToProduct X Y) e
  let h' := (F).map_isPushout h
  let : Epi e := terminal_from_axes_epi X Y
  let : Epi (Under.toSmash X Y) := h.epi_inl_of_epi
  let : Epi ((F).map (Under.toSmash X Y)) := (F).map_epi _
  let : Epi (reduction C (Under.smash X Y)) := inferInstanceAs (Epi (cokernel.π _))
  let : Epi (smashReduction X Y) := epi_comp _ _
  refine CokernelCofork.IsColimit.ofπ' _ _ (fun a ha => ?_)
  let b : (F).obj (Under.smash X Y).right ⟶ _ :=
    h'.desc a 0 (by simpa only [comp_zero] using ha)
  have hb : (F).map (Under.toSmash X Y) ≫ b = a := h'.inl_desc _ _ _
  have hb' : (F).map (Under.smash X Y).hom ≫ b = 0 := h'.inr_desc _ _ _
  exact ⟨reductionDesc C (Under.smash X Y) b hb', by
    exact (Category.assoc _ _ _).trans
      ((congrArg ((F).map (Under.toSmash X Y) ≫ ·) (reduction_reductionDesc C _ b hb')).trans hb)⟩

private abbrev tensorRelations (X Y : PointedSimplicialPresheaf.{w + 1} C) :
    ((F).obj X.right ⊗ (F).obj (⊤_ _)) ⨿ ((F).obj (⊤_ _) ⊗ (F).obj Y.right) ⟶
      (F).obj X.right ⊗ (F).obj Y.right :=
  coprod.desc ((F).obj X.right ◁ (F).map Y.hom) ((F).map X.hom ▷ (F).obj Y.right)

private def reductionTensorIsCokernel (X Y : PointedSimplicialPresheaf.{w + 1} C) :
    IsColimit (CokernelCofork.ofπ (reduction C X ⊗ₘ reduction C Y)
      (show tensorRelations X Y ≫ (reduction C X ⊗ₘ reduction C Y) = 0 from by
        apply coprod.hom_ext
        · simp only [tensorRelations, coprod.inl_desc_assoc, comp_zero,
            MonoidalCategory.tensorHom_def', ← MonoidalCategory.whiskerLeft_comp_assoc,
            basepoint_reduction, MonoidalPreadditive.whiskerLeft_zero, zero_comp]
        · simp only [tensorRelations, coprod.inr_desc_assoc, comp_zero,
            MonoidalCategory.tensorHom_def, ← MonoidalCategory.comp_whiskerRight_assoc,
            basepoint_reduction, MonoidalPreadditive.zero_whiskerRight, zero_comp])) := by
  let a := CokernelCofork.ofπ (reduction C X) (basepoint_reduction C X)
  let b := CokernelCofork.ofπ (reduction C Y) (basepoint_reduction C Y)
  let h := CokernelCofork.isColimitTensor (c₁ := a) (c₂ := b)
    (cokernelIsCokernel ((F).map X.hom)) (cokernelIsCokernel ((F).map Y.hom))
  have hb : (coprod.braiding _ _).hom ≫ tensorRelations X Y =
      coprod.desc ((F).map X.hom ▷ (F).obj Y.right) ((F).obj X.right ◁ (F).map Y.hom) := by
    apply coprod.hom_ext <;> simp [tensorRelations]
  exact IsCokernel.ofIsoComp _ _ (coprod.braiding _ _) hb h

/-- Reduced free abelianization takes smash to the integral degreewise tensor. -/
@[no_expose]
def reducedSmashTensorIso (X Y : PointedSimplicialPresheaf.{w + 1} C) :
    (R).obj (Under.smash X Y) ≅ (R).obj X ⊗ (R).obj Y :=
  CokernelCofork.mapIsoOfIsColimit (smashReductionIsCokernel X Y)
    (reductionTensorIsCokernel X Y)
    (Arrow.isoMk' ((F).map (Under.axesToProduct X Y)) (tensorRelations X Y)
      (freeAxesTensorIso X Y) (freeAbelianProductTensorIso X.right Y.right)
      (freeAxesTensorIso_hom X Y))

/-- The comparison on the quotient is induced by the original product tensor map. -/
@[reassoc]
theorem smashReduction_reducedSmashTensorIso_hom (X Y : PointedSimplicialPresheaf.{w + 1} C) :
    (F).map (Under.toSmash X Y) ≫ reduction C (Under.smash X Y) ≫
        (reducedSmashTensorIso X Y).hom =
      (freeAbelianProductTensorIso X.right Y.right).hom ≫
        (reduction C X ⊗ₘ reduction C Y) := by
  rw [← Category.assoc]
  exact CokernelCofork.π_mapOfIsColimit (smashReductionIsCokernel X Y) _ _

/-- The reduced tensor comparison respects the original pointed maps. -/
@[reassoc]
theorem reducedSmashTensorIso_naturality {X X' Y Y' : PointedSimplicialPresheaf.{w + 1} C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (R).map (Under.smashMap f g) ≫ (reducedSmashTensorIso X' Y').hom =
      (reducedSmashTensorIso X Y).hom ≫ ((R).map f ⊗ₘ (R).map g) := by
  let h := IsPushout.of_hasPushout (Under.axesToProduct X Y)
    (terminal.from (X.right ⨿ Y.right))
  let : Epi (terminal.from (X.right ⨿ Y.right) : X.right ⨿ Y.right ⟶ ⊤_ (Cᵒᵖ ⥤ SSet.{w + 1})) :=
    terminal_from_axes_epi X Y
  let : Epi (Under.toSmash X Y) := h.epi_inl_of_epi
  let : Epi ((F).map (Under.toSmash X Y)) := (F).map_epi _
  let : Epi (reduction C (Under.smash X Y)) := inferInstanceAs (Epi (cokernel.π _))
  let : Epi (smashReduction X Y) := epi_comp _ _
  apply (cancel_epi (smashReduction X Y)).mp
  change ((F).map (Under.toSmash X Y) ≫ reduction C (Under.smash X Y)) ≫ _ =
    ((F).map (Under.toSmash X Y) ≫ reduction C (Under.smash X Y)) ≫ _
  simp only [Category.assoc, reduction_naturality_assoc, ← (F).map_comp_assoc,
    Under.toSmash_smashMap, (F).map_comp, smashReduction_reducedSmashTensorIso_hom_assoc,
    smashReduction_reducedSmashTensorIso_hom, freeAbelianProductTensorIso_naturality_assoc]
  rw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
    reduction_naturality, reduction_naturality]

end CategoryTheory.PointedSimplicialPresheaf
