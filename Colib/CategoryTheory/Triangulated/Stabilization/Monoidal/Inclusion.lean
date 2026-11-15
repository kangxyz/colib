/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Symmetric

/-! # The braided inclusion and the inverse twist object -/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

open MonoidalCategory BraidedCategory
open scoped MonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (L : C)
variable [(tensorRight L).Full] [(tensorRight L).Faithful]

local notation "S" => Stabilization (tensorRight L)
local notation "T" => tensorRight L
local notation "J" => inclusion (tensorRight L)
local infixr:70 " ⊗ₛ " => tensorObj L
local infixr:70 " ⊗ₛₘ " => tensorHom L

/-- The inclusion at any level represents a numerator map at that level. -/
lemma numeratorHom_atLevel (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    numeratorHom L (X := (atLevel T n).obj X) (Y := (atLevel T n).obj Y) rfl f =
      (atLevel T n).map f := by
  have hX : ((atLevel T n).obj X).level + 0 = n := Nat.add_zero _
  have hY : ((atLevel T n).obj Y).level + 0 = n := Nat.add_zero _
  apply (homAtOffsets L hX hY).injective
  have h : ((atLevel T n).obj X).level = ((atLevel T n).obj Y).level := rfl
  rw [homAtOffsets_numeratorHom L h hX hY f]
  simp only [homAtOffsets, Equiv.trans_apply, Iso.homCongr_apply]
  rw [homEquiv_atLevel_map T n f]
  have eX : stageCoordinateIso L ((atLevel T n).obj X) hX = atLevelStageIso T n X := by rfl
  have eY : stageCoordinateIso L ((atLevel T n).obj Y) hY = atLevelStageIso T n Y := by rfl
  rw [eX, eY]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

section Braided

variable [BraidedCategory C] (hL : (β_ L L).hom = 𝟙 _)

include hL in
/-- The denominator-zero inclusion commutes with the stable tensor on morphisms. -/
lemma inclusion_tensorHom {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (J).map f ⊗ₛₘ (J).map g = (J).map (f ⊗ₘ g) := by
  rw [← numeratorHom_atLevel L 0 f, ← numeratorHom_atLevel L 0 g,
    numeratorHom_tensorHom L hL]
  exact numeratorHom_atLevel L 0 (f ⊗ₘ g)

/-- The denominator-zero inclusion is strong monoidal with identity comparisons. -/
def inclusionCoreMonoidal :
    letI := monoidalCategory L hL
    (J).CoreMonoidal :=
  letI := monoidalCategory L hL
  { εIso := Iso.refl _
    μIso := fun _ _ => Iso.refl _
    μIso_hom_natural_left := by
      intro X Y f Z
      change ((J).map f ⊗ₛₘ 𝟙 ((J).obj Z)) ≫ 𝟙 _ = 𝟙 _ ≫ (J).map (f ▷ Z)
      rw [Category.comp_id, Category.id_comp, ← (J).map_id,
        inclusion_tensorHom L hL, MonoidalCategory.tensorHom_id]
    μIso_hom_natural_right := by
      intro X Y Z f
      change (𝟙 ((J).obj Z) ⊗ₛₘ (J).map f) ≫ 𝟙 _ = 𝟙 _ ≫ (J).map (Z ◁ f)
      rw [Category.comp_id, Category.id_comp, ← (J).map_id,
        inclusion_tensorHom L hL, id_tensorHom]
    associativity := by
      intro X Y Z
      change (𝟙 ((J).obj (X ⊗ Y)) ⊗ₛₘ 𝟙 ((J).obj Z)) ≫ 𝟙 _ ≫
          (J).map (X := (X ⊗ Y) ⊗ Z) (Y := X ⊗ (Y ⊗ Z)) (α_ X Y Z).hom =
        (tensorAssociator L ((J).obj X) ((J).obj Y) ((J).obj Z)).hom ≫
          (𝟙 ((J).obj X) ⊗ₛₘ 𝟙 ((J).obj (Y ⊗ Z))) ≫ 𝟙 _
      simp only [tensorHom_id L hL, tensorObj, atLevel, Category.id_comp, Category.comp_id]
      exact (numeratorHom_atLevel L 0 (α_ X Y Z).hom).symm
    left_unitality := by
      intro X
      change (tensorLeftUnitor L ((J).obj X)).hom =
        (𝟙 ((J).obj (𝟙_ C)) ⊗ₛₘ 𝟙 ((J).obj X)) ≫ 𝟙 _ ≫
          (J).map (X := 𝟙_ C ⊗ X) (Y := X) (λ_ X).hom
      simp only [tensorHom_id L hL, tensorObj, atLevel, Category.id_comp]
      exact numeratorHom_atLevel L 0 (λ_ X).hom
    right_unitality := by
      intro X
      change (tensorRightUnitor L ((J).obj X)).hom =
        (𝟙 ((J).obj X) ⊗ₛₘ 𝟙 ((J).obj (𝟙_ C))) ≫ 𝟙 _ ≫
          (J).map (X := X ⊗ 𝟙_ C) (Y := X) (ρ_ X).hom
      simp only [tensorHom_id L hL, tensorObj, atLevel, Category.id_comp]
      exact numeratorHom_atLevel L 0 (ρ_ X).hom }

/-- The strong monoidal structure on the inclusion at denominator zero. -/
@[instance_reducible]
def inclusionMonoidal :
    letI := monoidalCategory L hL
    (J).Monoidal :=
  letI := monoidalCategory L hL
  (inclusionCoreMonoidal L hL).toMonoidal

end Braided

section Symmetric

variable [SymmetricCategory C] (hL : (β_ L L).hom = 𝟙 _)

/-- The denominator-zero inclusion preserves the braiding. -/
@[instance_reducible]
def inclusionBraided :
    letI := monoidalCategory L hL
    letI := symmetricCategory L hL
    (J).Braided :=
  letI := monoidalCategory L hL
  letI := symmetricCategory L hL
  { toMonoidal := inclusionMonoidal L hL
    braided X Y := by
      change 𝟙 _ ≫ (J).map (β_ X Y).hom =
        (tensorBraiding L ((J).obj X) ((J).obj Y)).hom ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
      exact (numeratorHom_atLevel L 0 (β_ X Y).hom).symm }

end Symmetric

/-- The inverse twist object has the tensor unit as numerator and denominator one. -/
def inverseTensorObject : S := ⟨𝟙_ C, 1⟩

/-- The included twist times its inverse is the stable tensor unit. -/
def tensorInverseIso : ((J).obj L ⊗ₛ inverseTensorObject L) ≅ tensorUnit L := by
  refine isoOfStage T _ _ 1 (Nat.le_refl 1) (Nat.zero_le 1) ?_
  exact ρ_ L ≪≫ (λ_ L).symm

/-- The inverse times the included twist is the stable tensor unit. -/
def inverseTensorIso : (inverseTensorObject L ⊗ₛ (J).obj L) ≅ tensorUnit L := by
  refine isoOfStage T _ _ 1 (Nat.le_refl 1) (Nat.zero_le 1) ?_
  exact Iso.refl (𝟙_ C ⊗ L)

end CategoryTheory.Stabilization
