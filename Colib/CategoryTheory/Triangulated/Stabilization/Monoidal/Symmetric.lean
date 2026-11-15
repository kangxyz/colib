/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Basic

/-! # Symmetric monoidal stabilization by an object of trivial self-braiding -/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

open MonoidalCategory BraidedCategory
open scoped MonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable (L : C) [(tensorRight L).Full] [(tensorRight L).Faithful]
variable (hL : (β_ L L).hom = 𝟙 _)

local notation "S" => Stabilization (tensorRight L)
local notation "T" => tensorRight L
local infixr:70 " ⊗ₛ " => tensorObj L
local infixr:70 " ⊗ₛₘ " => tensorHom L

include hL

/-- The stable braiding is natural in both arguments. -/
lemma tensorBraiding_naturality {X X' Y Y' : S} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₛₘ g) ≫ (tensorBraiding L X' Y').hom =
      (tensorBraiding L X Y).hom ≫ (g ⊗ₛₘ f) := by
  let n := max X.level X'.level
  let m := max Y.level Y'.level
  have hx : X.level + (n - X.level) = n := Nat.add_sub_of_le (Nat.le_max_left _ _)
  have hx' : X'.level + (n - X'.level) = n := Nat.add_sub_of_le (Nat.le_max_right _ _)
  have hy : Y.level + (m - Y.level) = m := Nat.add_sub_of_le (Nat.le_max_left _ _)
  have hy' : Y'.level + (m - Y'.level) = m := Nat.add_sub_of_le (Nat.le_max_right _ _)
  have ha := tensorOffset L hx hy
  have ha' := tensorOffset L hx' hy'
  have hb := (tensorOffset L hy hx).trans (Nat.add_comm m n)
  have hb' := (tensorOffset L hy' hx').trans (Nat.add_comm m n)
  apply (homAtOffsets L ha hb').injective
  rw [homAtOffsets_comp L ha ha' hb', homAtOffsets_comp L ha hb hb',
    homAtOffsets_tensorHom L hL hx hx' hy hy', homAtOffsets_tensorBraiding L hL hx hy,
    homAtOffsets_tensorBraiding L hL hx' hy',
    homAtOffsets_reindex L (tensorOffset L hy hx) (tensorOffset L hy' hx') (Nat.add_comm m n),
    homAtOffsets_tensorHom L hL hy hy' hx hx']
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [braiding_naturality_assoc]

/-- The stable braiding satisfies the first hexagon identity. -/
lemma tensorHexagon_forward (X Y Z : S) :
    (tensorAssociator L X Y Z).hom ≫ (tensorBraiding L X (Y ⊗ₛ Z)).hom ≫
        (tensorAssociator L Y Z X).hom =
      ((tensorBraiding L X Y).hom ⊗ₛₘ 𝟙 Z) ≫ (tensorAssociator L Y X Z).hom ≫
        (𝟙 Y ⊗ₛₘ (tensorBraiding L X Z).hom) := by
  simp only [tensorAssociator, tensorBraiding, numeratorIso]
  rw [← numeratorHom_id L Z, ← numeratorHom_id L Y]
  simp only [numeratorHom_tensorHom L hL, numeratorHom_comp]
  congr 1
  exact (by simpa only [tensorObj, MonoidalCategory.tensorHom_id, id_tensorHom] using
    (BraidedCategory.hexagon_forward X.obj Y.obj Z.obj))

/-- The stable braiding satisfies the second hexagon identity. -/
lemma tensorHexagon_reverse (X Y Z : S) :
    (tensorAssociator L X Y Z).inv ≫ (tensorBraiding L (X ⊗ₛ Y) Z).hom ≫
        (tensorAssociator L Z X Y).inv =
      (𝟙 X ⊗ₛₘ (tensorBraiding L Y Z).hom) ≫ (tensorAssociator L X Z Y).inv ≫
        ((tensorBraiding L X Z).hom ⊗ₛₘ 𝟙 Y) := by
  simp only [tensorAssociator, tensorBraiding, numeratorIso]
  rw [← numeratorHom_id L X, ← numeratorHom_id L Y]
  simp only [numeratorHom_tensorHom L hL, numeratorHom_comp]
  congr 1
  exact (by simpa only [tensorObj, MonoidalCategory.tensorHom_id, id_tensorHom] using
    (BraidedCategory.hexagon_reverse X.obj Y.obj Z.obj))

omit hL in
/-- Stable braidings in opposite orders cancel. -/
lemma tensorSymmetry (X Y : S) :
    (tensorBraiding L X Y).hom ≫ (tensorBraiding L Y X).hom = 𝟙 (X ⊗ₛ Y) := by
  simp only [tensorBraiding, numeratorIso]
  rw [numeratorHom_comp, SymmetricCategory.symmetry]
  exact numeratorHom_id L (X ⊗ₛ Y)

/-- The symmetric monoidal structure on stabilization by a tensor twist. -/
@[instance_reducible]
def symmetricCategory :
    letI := monoidalCategory L hL
    SymmetricCategory S :=
  letI := monoidalCategory L hL
  { braiding := tensorBraiding L
    braiding_naturality_right := fun X _ _ f => tensorBraiding_naturality L hL (𝟙 X) f
    braiding_naturality_left := fun f Z => tensorBraiding_naturality L hL f (𝟙 Z)
    hexagon_forward := tensorHexagon_forward L hL
    hexagon_reverse := tensorHexagon_reverse L hL
    symmetry := tensorSymmetry L }

end CategoryTheory.Stabilization
