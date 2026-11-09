/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.Functoriality
public import Colib.CategoryTheory.GroupCompletion.DiagonalAction

/-!
Implementation provenance: adapted from `Quillen/CategoryTheory/GroupCompletion/Switch.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual objects and maps.
 # The actual coordinate switch on the double action category -/
@[expose] public section
universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Coordinate exchange commutes with the diagonal left action. -/
instance swapLinear : (CategoryTheory.Prod.swap C C).LaxLeftLinear C where
  μₗ s X := 𝟙 _
  μₗ_naturality_left f X := by apply Prod.ext <;> simp <;> rfl
  μₗ_naturality_right s _ _ f := by apply Prod.ext <;> simp <;> rfl
  μₗ_associativity s t X := by apply Prod.ext <;> simp <;> rfl
  μₗ_unitality X := by apply Prod.ext <;> simp <;> rfl

/-- Switch the two coordinates without changing the common denominator. -/
def switch : Localization C C ⥤ Localization C C :=
  ActionLocalization.mapFunctor (CategoryTheory.Prod.swap C C)

@[simp]
lemma switch_obj (X : Localization C C) : switch.obj X = ⟨(X.obj.2, X.obj.1)⟩ := rfl

@[simp]
lemma switch_mkHom {X Y : C × C} (s : C)
    (f : s ⊗ X.1 ⟶ Y.1) (g : s ⊗ X.2 ⟶ Y.2) :
    switch.map (mkHom s f g) =
      mkHom (X := (X.2, X.1)) (Y := (Y.2, Y.1)) s g f := by
  change ActionLocalization.mkHom (X := (X.2, X.1)) (Y := (Y.2, Y.1))
    ⟨s, 𝟙 _ ≫ (g, f)⟩ = _
  rw [Category.id_comp]
  rfl

/-- Switching twice retains every original quotient morphism. -/
@[simp] lemma switch_map_switch {X Y : Localization C C} (f : X ⟶ Y) :
    switch.map (switch.map f) = f := by
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective X.obj Y.obj f
  change switch.map (switch.map (mkHom r.denom r.map.1 r.map.2)) = _
  rw [switch_mkHom]
  erw [switch_mkHom]
  rfl

/-- Switching twice is the original functor, including every quotient morphism. -/
lemma switch_comp_switch : switch (C := C) ⋙ switch = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  change switch.map (switch.map f) = 𝟙 _ ≫ f ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id, switch_map_switch]

/-- The coordinate switch is a genuine equivalence of the original categories. -/
def switchEquivalence : Localization C C ≌ Localization C C where
  functor := switch
  inverse := switch
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    change f ≫ 𝟙 _ = 𝟙 _ ≫ switch.map (switch.map f)
    rw [Category.id_comp, Category.comp_id, switch_map_switch])
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    change switch.map (switch.map f) ≫ 𝟙 _ = 𝟙 _ ≫ f
    rw [Category.id_comp, Category.comp_id, switch_map_switch])
  functor_unitIso_comp X := by
    change switch.map (𝟙 X) ≫ 𝟙 _ = 𝟙 _
    rw [Functor.map_id, Category.id_comp]

end CategoryTheory.GroupCompletion.Localization
