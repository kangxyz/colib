/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.FiniteDiagrams
public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Stages

/-! # Tensoring stable morphisms

Tensor maps are defined by realizing the two inputs separately and tensoring
the resulting maps. The stage transition theorem identifies this map with the
one computed at any other pair of admissible stages.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

open MonoidalCategory BraidedCategory
open scoped MonoidalCategory

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
variable (L : C) [(tensorRight L).Full] [(tensorRight L).Faithful]

local notation "S" => Stabilization (tensorRight L)
local notation "T" => tensorRight L

/-- Tensor two stable morphisms at the sum of their least common stages. -/
def tensorHom {X X' Y Y' : S} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorObj L X Y ⟶ tensorObj L X' Y' :=
  let n := max X.level X'.level
  let m := max Y.level Y'.level
  let hX : X.level ≤ n := Nat.le_max_left _ _
  let hX' : X'.level ≤ n := Nat.le_max_right _ _
  let hY : Y.level ≤ m := Nat.le_max_left _ _
  let hY' : Y'.level ≤ m := Nat.le_max_right _ _
  (homEquiv T _ _ (n + m) (Nat.add_le_add hX hY) (Nat.add_le_add hX' hY')).symm
    (tensorStageHom L hX hX' hY hY' (homEquiv T _ _ n hX hX' f) (homEquiv T _ _ m hY hY' g))

/-- A stable tensor map can be computed at any admissible pair of stages. -/
lemma homEquiv_tensorHom (hL : (β_ L L).hom = 𝟙 _)
    {X X' Y Y' : S} (f : X ⟶ X') (g : Y ⟶ Y') {n m : ℕ}
    (hX : X.level ≤ n) (hX' : X'.level ≤ n) (hY : Y.level ≤ m) (hY' : Y'.level ≤ m) :
    homEquiv T _ _ (n + m) (Nat.add_le_add hX hY) (Nat.add_le_add hX' hY')
      (tensorHom L f g) =
    tensorStageHom L hX hX' hY hY' (homEquiv T _ _ n hX hX' f) (homEquiv T _ _ m hY hY' g) := by
  dsimp only [tensorHom]
  have hn := max_le hX hX'
  have hm := max_le hY hY'
  let p := max X.level X'.level
  let q := max Y.level Y'.level
  have hpX : X.level ≤ p := Nat.le_max_left _ _
  have hpX' : X'.level ≤ p := Nat.le_max_right _ _
  have hqY : Y.level ≤ q := Nat.le_max_left _ _
  have hqY' : Y'.level ≤ q := Nat.le_max_right _ _
  change Hom.toStage (Hom.ofStage (p + q) (Nat.add_le_add hpX hqY)
      (Nat.add_le_add hpX' hqY')
      (tensorStageHom L hpX hpX' hqY hqY' (Hom.toStage f p hpX hpX')
        (Hom.toStage g q hqY hqY'))) (n + m) (Nat.add_le_add hX hY)
      (Nat.add_le_add hX' hY') = _
  rw [Hom.toStage_ofStage_of_le (h := Nat.add_le_add hn hm),
    tensorStageHom_transition L hL hpX hpX' hqY hqY' hn hm,
    Hom.toStage_trans, Hom.toStage_trans]
  rfl

/-- Tensoring identities gives the identity. -/
lemma tensorHom_id (hL : (β_ L L).hom = 𝟙 _) (X Y : S) :
    tensorHom L (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj L X Y) := by
  apply hom_ext T (X.level + Y.level) (Nat.le_refl _) (Nat.le_refl _)
  rw [homEquiv_tensorHom L hL _ _ (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _)]
  simp [tensorStageHom]

/-- Tensoring preserves simultaneous composition. -/
lemma tensorHom_comp (hL : (β_ L L).hom = 𝟙 _)
    {X X' X'' Y Y' Y'' : S} (f : X ⟶ X') (f' : X' ⟶ X'')
    (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    tensorHom L f g ≫ tensorHom L f' g' = tensorHom L (f ≫ f') (g ≫ g') := by
  let n := max (max X.level X'.level) X''.level
  let m := max (max Y.level Y'.level) Y''.level
  have hX : X.level ≤ n := by dsimp [n]; omega
  have hX' : X'.level ≤ n := by dsimp [n]; omega
  have hX'' : X''.level ≤ n := by dsimp [n]; omega
  have hY : Y.level ≤ m := by dsimp [m]; omega
  have hY' : Y'.level ≤ m := by dsimp [m]; omega
  have hY'' : Y''.level ≤ m := by dsimp [m]; omega
  apply hom_ext T (n + m) (Nat.add_le_add hX hY) (Nat.add_le_add hX'' hY'')
  rw [homEquiv_comp T _ _ _ (Nat.add_le_add hX hY) (Nat.add_le_add hX' hY')
      (Nat.add_le_add hX'' hY''),
    homEquiv_tensorHom L hL f g hX hX' hY hY',
    homEquiv_tensorHom L hL f' g' hX' hX'' hY' hY'',
    homEquiv_tensorHom L hL (f ≫ f') (g ≫ g') hX hX'' hY hY'',
    homEquiv_comp T f f' n hX hX' hX'', homEquiv_comp T g g' m hY hY' hY'']
  simp [tensorStageHom, Category.assoc]

/-- The stable tensor product as a functor of two variables. -/
def tensorBifunctor (hL : (β_ L L).hom = 𝟙 _) : S × S ⥤ S where
  obj X := tensorObj L X.1 X.2
  map f := tensorHom L f.1 f.2
  map_id X := tensorHom_id L hL X.1 X.2
  map_comp f g := (tensorHom_comp L hL f.1 g.1 f.2 g.2).symm

end CategoryTheory.Stabilization
