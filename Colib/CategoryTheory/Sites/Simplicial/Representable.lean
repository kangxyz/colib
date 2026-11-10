/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.PointedPresheaf

/-!
# The termwise Yoneda presheaf of a simplicial object

The value at a test object is the simplicial set of maps to the terms of
the original simplicial object. For a constant object the comparison with
discrete Yoneda is the identity on these maps in every degree.
-/

@[expose] public noncomputable section

open Opposite

universe v u

namespace CategoryTheory.SimplicialObject

variable (C : Type u) [Category.{v} C]

/-- Apply Yoneda termwise and put the test object first. -/
def termwiseYoneda : SimplicialObject C ⥤ Cᵒᵖ ⥤ SSet.{v} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ C (Cᵒᵖ ⥤ Type v)).obj CategoryTheory.yoneda ⋙
    flipFunctor SimplexCategoryᵒᵖ Cᵒᵖ (Type v)

@[simp]
theorem termwiseYoneda_obj_obj_obj (X : SimplicialObject C) (T : Cᵒᵖ)
    (n : SimplexCategoryᵒᵖ) :
    (((termwiseYoneda C).obj X).obj T).obj n = (T.unop ⟶ X.obj n) :=
  rfl

@[simp]
theorem termwiseYoneda_obj_obj_map_apply (X : SimplicialObject C) (T : Cᵒᵖ)
    {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) (g : T.unop ⟶ X.obj m) :
    (((termwiseYoneda C).obj X).obj T).map f g = g ≫ X.map f :=
  rfl

@[simp]
theorem termwiseYoneda_obj_map_app_apply (X : SimplicialObject C)
    {T U : Cᵒᵖ} (f : T ⟶ U) (n : SimplexCategoryᵒᵖ) (g : T.unop ⟶ X.obj n) :
    (((termwiseYoneda C).obj X).map f).app n g = f.unop ≫ g :=
  rfl

@[simp]
theorem termwiseYoneda_map_app_app_apply {X Y : SimplicialObject C} (f : X ⟶ Y)
    (T : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) (g : T.unop ⟶ X.obj n) :
    (((termwiseYoneda C).map f).app T).app n g = g ≫ f.app n :=
  rfl

/-- Termwise Yoneda on constant objects agrees naturally with discrete Yoneda. -/
def constTermwiseYonedaIso :
    SimplicialObject.const C ⋙ termwiseYoneda C ≅
      PointedSimplicialPresheaf.simplicialYoneda C :=
  NatIso.ofComponents
    (fun U => (flipFunctor SimplexCategoryᵒᵖ Cᵒᵖ (Type v)).mapIso
      (Functor.constComp SimplexCategoryᵒᵖ U CategoryTheory.yoneda))
    (by
      intro U V f
      apply NatTrans.ext
      funext T
      apply SSet.hom_ext
      intro n
      change (CategoryTheory.yoneda.map f).app T ≫ 𝟙 _ =
        𝟙 _ ≫ (CategoryTheory.yoneda.map f).app T
      rw [Category.comp_id, Category.id_comp])

@[simp]
theorem constTermwiseYonedaIso_hom_app_app_app (X : C) (T : Cᵒᵖ)
    (n : SimplexCategoryᵒᵖ) :
    (((constTermwiseYonedaIso C).hom.app X).app T).app n = 𝟙 (T.unop ⟶ X) :=
  rfl

end CategoryTheory.SimplicialObject
