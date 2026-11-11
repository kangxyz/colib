/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.CategoryTheory.Waldhausen.SConstruction.NerveCylinderInterchange

open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen
open scoped Simplicial
universe u v u' v'
noncomputable section

example {D : Type u} [Category.{v} D] {n m : SimplexCategory}
    {A B : Grid₂ n m ⥤ D} (η : A ⟶ B) (τ : m ⟶ ⦋1⦌) (p : Grid₂ n m) :
    (nerveCylinderDiagram η τ).obj p =
      ((ComposableArrows.mk₁ η).obj (τ.toOrderHom p.1)).obj p :=
  nerveCylinderDiagram_obj η τ p

example {D : Type u} [Category.{v} D] {n m : SimplexCategory}
    {A B : Grid₂ n m ⥤ D} (η : A ⟶ B) (τ : m ⟶ ⦋1⦌)
    {p q : Grid₂ n m} (f : p ⟶ q) :
    (nerveCylinderDiagram η τ).map f =
      ((ComposableArrows.mk₁ η).map ((nerveTimeFunctor n τ).map f)).app p ≫
        ((ComposableArrows.mk₁ η).obj (τ.toOrderHom q.1)).map f :=
  nerveCylinderDiagram_map η τ f

example {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F G : C ⥤ D} (η : F ⟶ G) (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D)
    (hF : ∀ X, F.map (α.app X) = β.app (F.obj X))
    (hG : ∀ X, G.map (α.app X) = β.app (G.obj X))
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ C) (τ θ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram
        (whiskerLeft (nerveCylinderDiagram (whiskerLeft A α) τ) η) θ =
      nerveCylinderDiagram
        (whiskerLeft (nerveCylinderDiagram (whiskerLeft A η) θ) β) τ :=
  nerveCylinderDiagram_identityAction_interchange η α β hF hG A τ θ
