/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveCylinder

/-!
# Isomorphic original nerve cylinders

A commuting square with isomorphic vertical sides induces an isomorphism of the entire original
nerve cylinder. The proof applies the actual uncurry functor to the isomorphism of coefficient
arrows, so the crossing maps and all original grid maps are retained.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor
open scoped Simplicial
universe u v u' v'
namespace CategoryTheory.Waldhausen

/-- The whole nerve-cylinder comparison induced by an actual isomorphism of its arrows. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/NerveCylinderIsomorphism.lean:25"
  "adaptation" "Original coefficient prism and independent ordinal naturality"]
def nerveCylinderDiagramIso {D : Type u} [Category.{v} D]
    {n m : SimplexCategory} {A B A' B' : Grid₂ n m ⥤ D}
    (η : A ⟶ B) (η' : A' ⟶ B') (eA : A ≅ A') (eB : B ≅ B')
    (h : η ≫ eB.hom = eA.hom ≫ η') (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram η τ ≅ nerveCylinderDiagram η' τ :=
  Functor.isoWhiskerLeft ((nerveTimeFunctor n τ).prod' (𝟭 (Grid₂ n m)))
    (Functor.uncurry.mapIso (ComposableArrows.isoMk₁ eA eB h))

/-- The component is the original coefficient-arrow comparison at the unchanged nerve time. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/NerveCylinderIsomorphism.lean:34"
  "adaptation" "Original coefficient prism and independent ordinal naturality"]
theorem nerveCylinderDiagramIso_hom_app {D : Type u} [Category.{v} D]
    {n m : SimplexCategory} {A B A' B' : Grid₂ n m ⥤ D}
    (η : A ⟶ B) (η' : A' ⟶ B') (eA : A ≅ A') (eB : B ≅ B')
    (h : η ≫ eB.hom = eA.hom ≫ η') (τ : m ⟶ ⦋1⦌) (p : Grid₂ n m) :
    (nerveCylinderDiagramIso η η' eA eB h τ).hom.app p =
      ((ComposableArrows.isoMk₁ (F := ComposableArrows.mk₁ η)
        (G := ComposableArrows.mk₁ η') eA eB h).hom.app (τ.toOrderHom p.1)).app p := rfl

/-- Uncurrying the actual coefficient arrow against an independent input grid is its nerve
cylinder, with no change to either parameter. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/NerveCylinderIsomorphism.lean:44"
  "adaptation" "Original coefficient prism and independent ordinal naturality"]
theorem nerveCylinderDiagram_whiskerLeft {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F G : C ⥤ D} (η : F ⟶ G)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ C) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram (whiskerLeft A η) τ =
      (nerveTimeFunctor n τ).prod' A ⋙ Functor.uncurry.obj (ComposableArrows.mk₁ η) := by
  have h : ComposableArrows.mk₁ (whiskerLeft A η) =
      ComposableArrows.mk₁ η ⋙ (whiskeringLeft _ _ _).obj A := by
    apply ComposableArrows.ext₁ (F := ComposableArrows.mk₁ (whiskerLeft A η))
      (G := ComposableArrows.mk₁ η ⋙ (whiskeringLeft _ _ _).obj A) rfl rfl
    simp
  unfold nerveCylinderDiagram
  rw [h]
  rfl

end CategoryTheory.Waldhausen
