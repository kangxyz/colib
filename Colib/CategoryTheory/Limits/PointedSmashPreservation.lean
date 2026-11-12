/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Limits.PointedSmash
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Preservation of the pointed smash quotient

A functor preserving finite limits and finite colimits carries the
product axes and their collapse to the same axes and quotient in the
target category. The comparison retains the actual maps of both factors.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe v v' u u'

namespace CategoryTheory.Under

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [HasTerminal C]
  {D : Type u'} [Category.{v'} D] [HasTerminal D]
  (F : C ⥤ D) [PreservesLimit (Functor.empty.{0} C) F]

/-- Apply a functor preserving terminal objects to an object with its specified point. -/
abbrev mapPointed : Under (⊤_ C) ⥤ Under (⊤_ D) :=
  Under.post F ⋙ Under.map (PreservesTerminal.iso F).inv

@[simp]
theorem mapPointed_obj_right (X : Under (⊤_ C)) : ((mapPointed F).obj X).right = F.obj X.right :=
  rfl

@[simp]
theorem mapPointed_obj_hom (X : Under (⊤_ C)) :
    ((mapPointed F).obj X).hom = (PreservesTerminal.iso F).inv ≫ F.map X.hom :=
  rfl

theorem mapPointed_map_right {X Y : Under (⊤_ C)} (f : X ⟶ Y) :
    ((mapPointed F).map f).right = F.map f.right :=
  rfl

variable [HasBinaryProducts C] [HasBinaryCoproducts C]
  [HasBinaryProducts D] [HasBinaryCoproducts D]

private theorem coprodComparison_map_axesToProduct_prodComparison (X Y : Under (⊤_ C)) :
    coprodComparison F X.right Y.right ≫ F.map (axesToProduct X Y) ≫
        prodComparison F X.right Y.right =
      axesToProduct ((mapPointed F).obj X) ((mapPointed F).obj Y) := by
  have ht (A : C) : F.map (terminal.from A) =
      terminal.from (F.obj A) ≫ (PreservesTerminal.iso F).inv := by
    apply (cancel_mono (PreservesTerminal.iso F).hom).1
    exact (terminal.hom_ext _ _).trans (by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  let t := PreservesTerminal.iso F
  change _ = coprod.desc
    (prod.lift (𝟙 (F.obj X.right)) (terminal.from (F.obj X.right) ≫ t.inv ≫ F.map Y.hom))
    (prod.lift (terminal.from (F.obj Y.right) ≫ t.inv ≫ F.map X.hom) (𝟙 (F.obj Y.right)))
  apply coprod.hom_ext
  · simp only [inl_coprodComparison_assoc, ← F.map_comp_assoc, axesToProduct, coprod.inl_desc]
    apply prod.hom_ext
    · rw [Category.assoc, prodComparison_fst, ← F.map_comp, prod.lift_fst,
        F.map_id, prod.lift_fst]
    · rw [Category.assoc, prodComparison_snd, ← F.map_comp, prod.lift_snd,
        prod.lift_snd, F.map_comp, ht, Category.assoc]
  · simp only [inr_coprodComparison_assoc, ← F.map_comp_assoc, axesToProduct, coprod.inr_desc]
    apply prod.hom_ext
    · rw [Category.assoc, prodComparison_fst, ← F.map_comp, prod.lift_fst,
        prod.lift_fst, F.map_comp, ht, Category.assoc]
    · rw [Category.assoc, prodComparison_snd, ← F.map_comp, prod.lift_snd,
        F.map_id, prod.lift_snd]

variable [HasPushouts C]
  [PreservesLimitsOfShape (Discrete WalkingPair) F] [PreservesFiniteColimits F]

private theorem mappedSmashIsPushout (X Y : Under (⊤_ C)) :
    IsPushout (axesToProduct ((mapPointed F).obj X) ((mapPointed F).obj Y))
      (terminal.from _)
      ((PreservesLimitPair.iso F X.right Y.right).inv ≫ F.map (toSmash X Y))
      ((mapPointed F).obj (smash X Y)).hom := by
  let eC := PreservesColimitPair.iso F X.right Y.right
  let eP := PreservesLimitPair.iso F X.right Y.right
  let eT := PreservesTerminal.iso F
  have h := F.map_isPushout
    (IsPushout.of_hasPushout (axesToProduct X Y) (terminal.from (X.right ⨿ Y.right)))
  refine h.of_iso eC.symm eP eT (Iso.refl _) ?_ (terminal.hom_ext _ _) ?_ ?_
  · apply (cancel_epi eC.hom).1
    rw [Iso.symm_hom, Iso.hom_inv_id_assoc]
    exact coprodComparison_map_axesToProduct_prodComparison F X Y
  · change F.map (toSmash X Y) ≫ 𝟙 _ = eP.hom ≫ eP.inv ≫ F.map (toSmash X Y)
    rw [Category.comp_id, Iso.hom_inv_id_assoc]
  · change F.map (smash X Y).hom ≫ 𝟙 _ = eT.hom ≫ eT.inv ≫ F.map (smash X Y).hom
    rw [Category.comp_id, Iso.hom_inv_id_assoc]

variable [HasPushouts D]

/-- The image of the original smash is the smash of the transported pointed objects. -/
@[no_expose]
def mapPointedSmashIso (X Y : Under (⊤_ C)) :
    smash ((mapPointed F).obj X) ((mapPointed F).obj Y) ≅ (mapPointed F).obj (smash X Y) :=
  let h := IsPushout.of_hasPushout (axesToProduct ((mapPointed F).obj X) ((mapPointed F).obj Y))
    (terminal.from _)
  Under.isoMk (h.isoIsPushout _ _ (mappedSmashIsPushout F X Y))
    (h.inr_isoIsPushout_hom _ _ (mappedSmashIsPushout F X Y))

@[reassoc]
theorem toSmash_mapPointedSmashIso_hom (X Y : Under (⊤_ C)) :
    toSmash ((mapPointed F).obj X) ((mapPointed F).obj Y) ≫
        (mapPointedSmashIso F X Y).hom.right =
      (PreservesLimitPair.iso F X.right Y.right).inv ≫ F.map (toSmash X Y) :=
  (IsPushout.of_hasPushout (axesToProduct _ _) (terminal.from _)).inl_isoIsPushout_hom
    _ _ (mappedSmashIsPushout F X Y)

@[reassoc]
theorem mapPointedSmashIso_naturality {X X' Y Y' : Under (⊤_ C)} (f : X ⟶ X') (g : Y ⟶ Y') :
    smashMap ((mapPointed F).map f) ((mapPointed F).map g) ≫ (mapPointedSmashIso F X' Y').hom =
      (mapPointedSmashIso F X Y).hom ≫ (mapPointed F).map (smashMap f g) := by
  have h : (PreservesLimitPair.iso F X.right Y.right).inv ≫ F.map (prod.map f.right g.right) =
      prod.map (F.map f.right) (F.map g.right) ≫
        (PreservesLimitPair.iso F X'.right Y'.right).inv := by
    apply (cancel_mono (PreservesLimitPair.iso F X'.right Y'.right).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change (PreservesLimitPair.iso F X.right Y.right).inv ≫
        F.map (prod.map f.right g.right) ≫ prodComparison F X'.right Y'.right =
      prod.map (F.map f.right) (F.map g.right)
    rw [prodComparison_natural, ← PreservesLimitPair.iso_hom, Iso.inv_hom_id_assoc]
  apply smash_hom_ext
  rw [Under.comp_right, Under.comp_right, toSmash_smashMap_assoc,
    toSmash_mapPointedSmashIso_hom F X' Y',
    ← Category.assoc (toSmash ((mapPointed F).obj X) ((mapPointed F).obj Y)),
    toSmash_mapPointedSmashIso_hom F X Y, Category.assoc]
  change prod.map (F.map f.right) (F.map g.right) ≫
      (PreservesLimitPair.iso F X'.right Y'.right).inv ≫ F.map (toSmash X' Y') =
    (PreservesLimitPair.iso F X.right Y.right).inv ≫
      F.map (toSmash X Y) ≫ F.map (smashMap f g).right
  rw [← F.map_comp, toSmash_smashMap, F.map_comp, reassoc_of% h]

end CategoryTheory.Under
