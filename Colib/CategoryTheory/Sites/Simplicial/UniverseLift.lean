/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.PointedPresheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Universe lift of pointed simplicial presheaves

Postcomposition with the native simplicial universe lift raises the simplex
universe degreewise. The terminal comparison transports the global point
in the native under category.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe w' w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C]

/-- The degreewise universe lift of simplicial presheaves. -/
def uliftPresheaf : (Cᵒᵖ ⥤ SSet.{w}) ⥤ (Cᵒᵖ ⥤ SSet.{max w w'}) :=
  (Functor.whiskeringRight _ _ _).obj SSet.uliftFunctor.{w', w}

theorem uliftPresheaf_obj_obj_obj (F : Cᵒᵖ ⥤ SSet.{w}) (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    (((uliftPresheaf.{w', w} C).obj F).obj U).obj n = ULift.{w'} ((F.obj U).obj n) := rfl

/-- The lifted map applies the original map in each object and simplex degree. -/
@[simp]
theorem uliftPresheaf_map_app_app_apply {F G : Cᵒᵖ ⥤ SSet.{w}} (f : F ⟶ G)
    (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) (x : ULift.{w'} ((F.obj U).obj n)) :
    (((uliftPresheaf.{w', w} C).map f).app U).app n x = ULift.up ((f.app U).app n x.down) := rfl

/-- The native terminal comparison for the degreewise universe lift. -/
def uliftPresheafTerminalIso :
    (uliftPresheaf.{w', w} C).obj (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ≅
      ⊤_ (Cᵒᵖ ⥤ SSet.{max w w'}) := by
  letI : PreservesLimitsOfShape (Discrete.{0} PEmpty) SSet.uliftFunctor.{w', w} := by
    unfold SSet.uliftFunctor
    infer_instance
  letI : PreservesLimit (Functor.empty.{0} (Cᵒᵖ ⥤ SSet.{w})) (uliftPresheaf.{w', w} C) := by
    exact (whiskeringRight_preservesLimitsOfShape (C := Cᵒᵖ) (J := Discrete.{0} PEmpty)
      SSet.uliftFunctor.{w', w}).preservesLimit
  exact PreservesTerminal.iso _

/-- The universe lift of pointed simplicial presheaves, with the actual global point transported. -/
def uliftPointed : PointedSimplicialPresheaf.{w} C ⥤ PointedSimplicialPresheaf.{max w w'} C :=
  Under.post (X := ⊤_ (Cᵒᵖ ⥤ SSet.{w})) (uliftPresheaf.{w', w} C) ⋙
    Under.map (uliftPresheafTerminalIso.{w', w} C).inv

@[simp]
theorem uliftPointed_obj_right (F : PointedSimplicialPresheaf.{w} C) :
    ((uliftPointed.{w', w} C).obj F).right = (uliftPresheaf.{w', w} C).obj F.right := rfl

@[simp]
theorem uliftPointed_map_right {F G : PointedSimplicialPresheaf.{w} C} (f : F ⟶ G) :
    ((uliftPointed.{w', w} C).map f).right = (uliftPresheaf.{w', w} C).map f.right := rfl

/-- The new global point is the original one after universe lift and terminal transport. -/
@[simp]
theorem uliftPointed_obj_hom (F : PointedSimplicialPresheaf.{w} C) :
    ((uliftPointed.{w', w} C).obj F).hom =
      (uliftPresheafTerminalIso.{w', w} C).inv ≫ (uliftPresheaf.{w', w} C).map F.hom := rfl

end CategoryTheory.PointedSimplicialPresheaf
