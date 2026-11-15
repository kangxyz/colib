/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Additive
public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # Additivity of the tensor product in stabilization -/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

open MonoidalCategory BraidedCategory
open scoped MonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
variable [BraidedCategory C] [MonoidalPreadditive C] (L : C)
variable [(tensorRight L).Full] [(tensorRight L).Faithful]

local notation "S" => Stabilization (tensorRight L)
local notation "T" => tensorRight L
local infixr:70 " ⊗ₛₘ " => tensorHom L

variable (hL : (β_ L L).hom = 𝟙 _)

include hL

/-- Stable tensoring on the left preserves the zero morphism. -/
lemma tensorHom_zero_right {X X' Y Y' : S} (f : X ⟶ X') :
    f ⊗ₛₘ (0 : Y ⟶ Y') = 0 := by
  let n := max X.level X'.level
  let m := max Y.level Y'.level
  have hX : X.level ≤ n := Nat.le_max_left _ _
  have hX' : X'.level ≤ n := Nat.le_max_right _ _
  have hY : Y.level ≤ m := Nat.le_max_left _ _
  have hY' : Y'.level ≤ m := Nat.le_max_right _ _
  apply hom_ext T (n + m) (Nat.add_le_add hX hY) (Nat.add_le_add hX' hY')
  rw [homEquiv_tensorHom L hL f 0 hX hX' hY hY']
  simp [tensorStageHom]

/-- Stable tensoring on the right preserves the zero morphism. -/
lemma tensorHom_zero_left {X X' Y Y' : S} (g : Y ⟶ Y') :
    (0 : X ⟶ X') ⊗ₛₘ g = 0 := by
  let n := max X.level X'.level
  let m := max Y.level Y'.level
  have hX : X.level ≤ n := Nat.le_max_left _ _
  have hX' : X'.level ≤ n := Nat.le_max_right _ _
  have hY : Y.level ≤ m := Nat.le_max_left _ _
  have hY' : Y'.level ≤ m := Nat.le_max_right _ _
  apply hom_ext T (n + m) (Nat.add_le_add hX hY) (Nat.add_le_add hX' hY')
  rw [homEquiv_tensorHom L hL 0 g hX hX' hY hY']
  simp [tensorStageHom]

/-- Stable tensoring on the left preserves sums. -/
lemma tensorHom_add_right {X X' Y Y' : S} (f : X ⟶ X') (g g' : Y ⟶ Y') :
    f ⊗ₛₘ (g + g') = (f ⊗ₛₘ g) + (f ⊗ₛₘ g') := by
  let n := max X.level X'.level
  let m := max Y.level Y'.level
  have hX : X.level ≤ n := Nat.le_max_left _ _
  have hX' : X'.level ≤ n := Nat.le_max_right _ _
  have hY : Y.level ≤ m := Nat.le_max_left _ _
  have hY' : Y'.level ≤ m := Nat.le_max_right _ _
  apply hom_ext T (n + m) (Nat.add_le_add hX hY) (Nat.add_le_add hX' hY')
  rw [homEquiv_add, homEquiv_tensorHom L hL f (g + g') hX hX' hY hY',
    homEquiv_tensorHom L hL f g hX hX' hY hY', homEquiv_tensorHom L hL f g' hX hX' hY hY',
    homEquiv_add]
  simp only [tensorStageHom, MonoidalPreadditive.tensor_add, Preadditive.add_comp,
    Preadditive.comp_add]

/-- Stable tensoring on the right preserves sums. -/
lemma tensorHom_add_left {X X' Y Y' : S} (f f' : X ⟶ X') (g : Y ⟶ Y') :
    (f + f') ⊗ₛₘ g = (f ⊗ₛₘ g) + (f' ⊗ₛₘ g) := by
  let n := max X.level X'.level
  let m := max Y.level Y'.level
  have hX : X.level ≤ n := Nat.le_max_left _ _
  have hX' : X'.level ≤ n := Nat.le_max_right _ _
  have hY : Y.level ≤ m := Nat.le_max_left _ _
  have hY' : Y'.level ≤ m := Nat.le_max_right _ _
  apply hom_ext T (n + m) (Nat.add_le_add hX hY) (Nat.add_le_add hX' hY')
  rw [homEquiv_add, homEquiv_tensorHom L hL (f + f') g hX hX' hY hY',
    homEquiv_tensorHom L hL f g hX hX' hY hY', homEquiv_tensorHom L hL f' g hX hX' hY hY',
    homEquiv_add]
  simp only [tensorStageHom, MonoidalPreadditive.add_tensor, Preadditive.add_comp,
    Preadditive.comp_add]

/-- The tensor of stable morphisms is additive in both variables. -/
theorem monoidalPreadditive :
    letI := monoidalCategory L hL
    MonoidalPreadditive S :=
  letI := monoidalCategory L hL
  { whiskerLeft_zero := fun {X _ _} => tensorHom_zero_right L hL (𝟙 X)
    zero_whiskerRight := fun {X _ _} => tensorHom_zero_left L hL (𝟙 X)
    whiskerLeft_add := fun {X _ _} f g => tensorHom_add_right L hL (𝟙 X) f g
    add_whiskerRight := fun {X _ _} f g => tensorHom_add_left L hL f g (𝟙 X) }

end CategoryTheory.Stabilization
