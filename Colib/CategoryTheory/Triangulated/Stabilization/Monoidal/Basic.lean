/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Constraints

/-! # The monoidal structure of tensor stabilization -/

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
local notation "I" => iterateTensorObj L
local notation "P" => iterateTensorIso L
local infixr:70 " ⊗ₛ " => tensorObj L
local infixr:70 " ⊗ₛₘ " => tensorHom L

/-- The Hom identification is independent of the presentation of the common stage. -/
lemma homAtOffsets_reindex {X Y : S} {p q n n' : ℕ}
    (hX : X.level + p = n) (hY : Y.level + q = n) (h : n = n') :
    homAtOffsets L (hX.trans h) (hY.trans h) = homAtOffsets L hX hY := by
  subst n'
  rfl

/-- The numerator identity gives the identity. -/
@[simp]
lemma numeratorHom_id (X : S) : numeratorHom L rfl (𝟙 X.obj) = 𝟙 X := by
  have hX : X.level + 0 = X.level := Nat.add_zero _
  apply (homAtOffsets L hX hX).injective
  rw [homAtOffsets_numeratorHom L rfl hX hX, homAtOffsets_id]
  rfl

/-- Composition of numerator maps at equal denominators. -/
lemma numeratorHom_comp {X Y Z : S} (hXY : X.level = Y.level) (hYZ : Y.level = Z.level)
    (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj) :
    numeratorHom L hXY f ≫ numeratorHom L hYZ g = numeratorHom L (hXY.trans hYZ) (f ≫ g) := by
  have hX : X.level + 0 = X.level := Nat.add_zero _
  have hY : Y.level + 0 = X.level := (Nat.add_zero _).trans hXY.symm
  have hZ : Z.level + 0 = X.level := (Nat.add_zero _).trans (hXY.trans hYZ).symm
  apply (homAtOffsets L hX hZ).injective
  rw [homAtOffsets_comp L hX hY hZ, homAtOffsets_numeratorHom L hXY hX hY,
    homAtOffsets_numeratorHom L hYZ hY hZ, homAtOffsets_numeratorHom L (hXY.trans hYZ) hX hZ]
  rfl

section Braided

variable [BraidedCategory C] (hL : (β_ L L).hom = 𝟙 _)

include hL

/-- Tensoring numerator maps tensors their representatives. -/
lemma numeratorHom_tensorHom {X X' Y Y' : S} (hX : X.level = X'.level)
    (hY : Y.level = Y'.level) (f : X.obj ⟶ X'.obj) (g : Y.obj ⟶ Y'.obj) :
    numeratorHom L hX f ⊗ₛₘ numeratorHom L hY g =
      numeratorHom L (congrArg₂ (· + ·) hX hY) (f ⊗ₘ g) := by
  have hx : X.level + 0 = X.level := Nat.add_zero _
  have hx' : X'.level + 0 = X.level := (Nat.add_zero _).trans hX.symm
  have hy : Y.level + 0 = Y.level := Nat.add_zero _
  have hy' : Y'.level + 0 = Y.level := (Nat.add_zero _).trans hY.symm
  apply (homAtOffsets L (tensorOffset L hx hy) (tensorOffset L hx' hy')).injective
  rw [homAtOffsets_tensorHom L hL hx hx' hy hy',
    homAtOffsets_numeratorHom L hX hx hx', homAtOffsets_numeratorHom L hY hy hy',
    homAtOffsets_numeratorHom L (congrArg₂ (· + ·) hX hY)
      (tensorOffset L hx hy) (tensorOffset L hx' hy')]
  change 𝟙 _ ≫ (f ⊗ₘ g) ≫ 𝟙 _ = f ⊗ₘ g
  simp

private lemma homAtOffsets_tensorHom_at
    {X X' Y Y' : S} {p p' q q' n m k : ℕ}
    (hX : X.level + p = n) (hX' : X'.level + p' = n)
    (hY : Y.level + q = m) (hY' : Y'.level + q' = m)
    (hxy : (X ⊗ₛ Y).level + (p + q) = k)
    (hxy' : (X' ⊗ₛ Y').level + (p' + q') = k)
    (f : X ⟶ X') (g : Y ⟶ Y') :
    homAtOffsets L hxy hxy' (f ⊗ₛₘ g) =
      (P X.obj Y.obj p q).inv ≫
        (homAtOffsets L hX hX' f ⊗ₘ homAtOffsets L hY hY' g) ≫
          (P X'.obj Y'.obj p' q').hom := by
  have h : n + m = k := (tensorOffset L hX hY).symm.trans hxy
  exact (congrFun (congrArg Equiv.toFun (homAtOffsets_reindex L
      (tensorOffset L hX hY) (tensorOffset L hX' hY') h)) (f ⊗ₛₘ g)).trans
    (homAtOffsets_tensorHom L hL hX hX' hY hY' f g)

/-- The stable associator is natural. -/
lemma tensorAssociator_naturality
    {X X' Y Y' Z Z' : S} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    ((f ⊗ₛₘ g) ⊗ₛₘ h) ≫ (tensorAssociator L X' Y' Z').hom =
      (tensorAssociator L X Y Z).hom ≫ (f ⊗ₛₘ (g ⊗ₛₘ h)) := by
  let n := max X.level X'.level
  let m := max Y.level Y'.level
  let k := max Z.level Z'.level
  have hn : X.level ≤ n := Nat.le_max_left _ _
  have hn' : X'.level ≤ n := Nat.le_max_right _ _
  have hm : Y.level ≤ m := Nat.le_max_left _ _
  have hm' : Y'.level ≤ m := Nat.le_max_right _ _
  have hk : Z.level ≤ k := Nat.le_max_left _ _
  have hk' : Z'.level ≤ k := Nat.le_max_right _ _
  have hx : X.level + (n - X.level) = n := Nat.add_sub_of_le hn
  have hx' : X'.level + (n - X'.level) = n := Nat.add_sub_of_le hn'
  have hy : Y.level + (m - Y.level) = m := Nat.add_sub_of_le hm
  have hy' : Y'.level + (m - Y'.level) = m := Nat.add_sub_of_le hm'
  have hz : Z.level + (k - Z.level) = k := Nat.add_sub_of_le hk
  have hz' : Z'.level + (k - Z'.level) = k := Nat.add_sub_of_le hk'
  have ha := tensorOffset L (tensorOffset L hx hy) hz
  have ha' := tensorOffset L (tensorOffset L hx' hy') hz'
  have hb := (tensorOffset L hx (tensorOffset L hy hz)).trans (Nat.add_assoc n m k).symm
  have hb' := (tensorOffset L hx' (tensorOffset L hy' hz')).trans (Nat.add_assoc n m k).symm
  apply (homAtOffsets L ha hb').injective
  rw [homAtOffsets_comp L ha ha' hb', homAtOffsets_comp L ha hb hb',
    homAtOffsets_tensorAssociator L hL hx hy hz, homAtOffsets_tensorAssociator L hL hx' hy' hz',
    homAtOffsets_tensorHom_at L hL (tensorOffset L hx hy) (tensorOffset L hx' hy') hz hz' ha ha',
    homAtOffsets_tensorHom L hL hx hx' hy hy',
    homAtOffsets_tensorHom_at L hL hx hx' (tensorOffset L hy hz) (tensorOffset L hy' hz') hb hb',
    homAtOffsets_tensorHom L hL hy hy' hz hz']
  simp only [tensorObj, Category.assoc, Iso.hom_inv_id_assoc,
    tensorHom_comp_whiskerRight_assoc, whiskerLeft_comp_tensorHom_assoc,
    Iso.hom_inv_id, Category.comp_id]
  rw [← whiskerRight_comp_tensorHom_assoc, associator_naturality_assoc,
    tensorHom_comp_whiskerLeft_assoc]

/-- The stable left unitor is natural. -/
lemma tensorLeftUnitor_naturality {X Y : S} (f : X ⟶ Y) :
    (𝟙 (tensorUnit L) ⊗ₛₘ f) ≫ (tensorLeftUnitor L Y).hom =
      (tensorLeftUnitor L X).hom ≫ f := by
  let n := max X.level Y.level
  have hx : X.level + (n - X.level) = n := Nat.add_sub_of_le (Nat.le_max_left _ _)
  have hy : Y.level + (n - Y.level) = n := Nat.add_sub_of_le (Nat.le_max_right _ _)
  have hu : (tensorUnit L).level + 0 = 0 := level_tensorUnit L
  have ha := tensorOffset L hu hx
  have ha' := tensorOffset L hu hy
  have hb := hx.trans (Nat.zero_add n).symm
  have hb' := hy.trans (Nat.zero_add n).symm
  apply (homAtOffsets L ha hb').injective
  rw [homAtOffsets_comp L ha ha' hb', homAtOffsets_comp L ha hb hb',
    homAtOffsets_tensorHom L hL hu hu hx hy, homAtOffsets_id,
    homAtOffsets_tensorLeftUnitor L hx, homAtOffsets_tensorLeftUnitor L hy]
  simp only [tensorObj, tensorUnit, Category.assoc, Iso.hom_inv_id_assoc]
  let g := homAtOffsets L hx hy f
  have hg : homAtOffsets L hb hb' f = g :=
    congrFun (congrArg Equiv.toFun (homAtOffsets_reindex L hx hy (Nat.zero_add n).symm)) f
  rw [hg]
  change _ ≫ (𝟙 (𝟙_ C) ⊗ₘ g) ≫ (λ_ _).hom = _
  rw [id_tensorHom, leftUnitor_naturality]

/-- The stable right unitor is natural. -/
lemma tensorRightUnitor_naturality {X Y : S} (f : X ⟶ Y) :
    (f ⊗ₛₘ 𝟙 (tensorUnit L)) ≫ (tensorRightUnitor L Y).hom =
      (tensorRightUnitor L X).hom ≫ f := by
  let n := max X.level Y.level
  have hx : X.level + (n - X.level) = n := Nat.add_sub_of_le (Nat.le_max_left _ _)
  have hy : Y.level + (n - Y.level) = n := Nat.add_sub_of_le (Nat.le_max_right _ _)
  have hu : (tensorUnit L).level + 0 = 0 := level_tensorUnit L
  have ha := tensorOffset L hx hu
  have ha' := tensorOffset L hy hu
  apply (homAtOffsets L ha hy).injective
  rw [homAtOffsets_comp L ha ha' hy, homAtOffsets_comp L ha hx hy,
    homAtOffsets_tensorHom L hL hx hy hu hu, homAtOffsets_id,
    homAtOffsets_tensorRightUnitor L hL hx, homAtOffsets_tensorRightUnitor L hL hy]
  simp only [tensorObj, tensorUnit, Category.assoc, Iso.hom_inv_id_assoc]
  let g := homAtOffsets L hx hy f
  change _ ≫ (g ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ _).hom = _
  rw [MonoidalCategory.tensorHom_id, rightUnitor_naturality]

/-- The stable associator satisfies the pentagon identity. -/
lemma tensorPentagon (W X Y Z : S) :
    ((tensorAssociator L W X Y).hom ⊗ₛₘ 𝟙 Z) ≫ (tensorAssociator L W (X ⊗ₛ Y) Z).hom ≫
        (𝟙 W ⊗ₛₘ (tensorAssociator L X Y Z).hom) =
      (tensorAssociator L (W ⊗ₛ X) Y Z).hom ≫ (tensorAssociator L W X (Y ⊗ₛ Z)).hom := by
  simp only [tensorAssociator, numeratorIso]
  rw [← numeratorHom_id L Z, ← numeratorHom_id L W]
  simp only [numeratorHom_tensorHom L hL, numeratorHom_comp]
  congr 1
  exact (by simpa only [tensorObj, tensorUnit, MonoidalCategory.tensorHom_id, id_tensorHom] using
    (MonoidalCategory.pentagon W.obj X.obj Y.obj Z.obj))

/-- The stable unitors and associator satisfy the triangle identity. -/
lemma tensorTriangle (X Y : S) :
    (tensorAssociator L X (tensorUnit L) Y).hom ≫ (𝟙 X ⊗ₛₘ (tensorLeftUnitor L Y).hom) =
      (tensorRightUnitor L X).hom ⊗ₛₘ 𝟙 Y := by
  simp only [tensorAssociator, tensorLeftUnitor, tensorRightUnitor, numeratorIso]
  rw [← numeratorHom_id L X, ← numeratorHom_id L Y]
  simp only [numeratorHom_tensorHom L hL, numeratorHom_comp]
  congr 1
  exact (by simpa only [tensorObj, tensorUnit, MonoidalCategory.tensorHom_id, id_tensorHom] using
    (MonoidalCategory.triangle X.obj Y.obj))

omit hL in
/-- The tensor, unit and coherence isomorphisms on the underlying stabilization. -/
@[instance_reducible]
def monoidalCategoryStruct : MonoidalCategoryStruct S where
  tensorObj := tensorObj L
  tensorHom := tensorHom L
  whiskerLeft X _ _ f := 𝟙 X ⊗ₛₘ f
  whiskerRight f X := f ⊗ₛₘ 𝟙 X
  tensorUnit := tensorUnit L
  associator := tensorAssociator L
  leftUnitor := tensorLeftUnitor L
  rightUnitor := tensorRightUnitor L

/-- Stabilization by tensoring with an object of trivial self-braiding is monoidal. -/
@[instance_reducible]
def monoidalCategory : MonoidalCategory S :=
  letI := monoidalCategoryStruct L
  MonoidalCategory.ofTensorHom
    (tensorHom_id L hL) (by intros; rfl) (by intros; rfl)
    (fun f g f' g' => tensorHom_comp L hL f f' g g')
    (fun f g h => tensorAssociator_naturality L hL f g h)
    (tensorLeftUnitor_naturality L hL) (tensorRightUnitor_naturality L hL)
    (tensorPentagon L hL) (tensorTriangle L hL)

end Braided

end CategoryTheory.Stabilization
