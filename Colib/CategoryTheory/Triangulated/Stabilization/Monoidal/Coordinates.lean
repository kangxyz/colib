/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Tensor

/-! # Realization with specified numbers of twists -/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

open MonoidalCategory BraidedCategory
open scoped MonoidalCategory

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (L : C)

local notation "S" => Stabilization (tensorRight L)
local notation "T" => tensorRight L
local notation "I" => iterateTensorObj L

/-- The denominator of the tensor product is the sum of the two denominators. -/
@[simp]
lemma level_tensorObj (X Y : S) : (tensorObj L X Y).level = X.level + Y.level := rfl

/-- Tensor products add the specified twist counts as well as the realization levels. -/
lemma tensorOffset {X Y : S} {p q n m : ℕ}
    (hX : X.level + p = n) (hY : Y.level + q = m) :
    (tensorObj L X Y).level + (p + q) = n + m := by
  simp only [level_tensorObj]
  omega

variable [(tensorRight L).Full] [(tensorRight L).Faithful]

/-- Use an explicit number of twists in a realization. -/
def stageCoordinateIso (X : S) {p n : ℕ} (h : X.level + p = n) :
    stage T X n ≅ I p X.obj :=
  eqToIso (congrArg (fun k => I k X.obj) (by omega : n - X.level = p))

/-- The stable Hom equivalence with the twist counts given explicitly. -/
def homAtOffsets {X Y : S} {p q n : ℕ} (hX : X.level + p = n) (hY : Y.level + q = n) :
    (X ⟶ Y) ≃ (I p X.obj ⟶ I q Y.obj) :=
  (homEquiv T X Y n (by omega) (by omega)).trans
    ((stageCoordinateIso L X hX).homCongr (stageCoordinateIso L Y hY))

/-- Realization of an identity. -/
@[simp]
lemma homAtOffsets_id {X : S} {p n : ℕ} (hX : X.level + p = n) :
    homAtOffsets L hX hX (𝟙 X) = 𝟙 (I p X.obj) := by
  simp [homAtOffsets]

/-- Realization of a composite. -/
lemma homAtOffsets_comp {X Y Z : S} {p q r n : ℕ}
    (hX : X.level + p = n) (hY : Y.level + q = n) (hZ : Z.level + r = n)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homAtOffsets L hX hZ (f ≫ g) = homAtOffsets L hX hY f ≫ homAtOffsets L hY hZ g := by
  simp only [homAtOffsets, Equiv.trans_apply]
  rw [homEquiv_comp T f g n (by omega) (by omega) (by omega), Iso.homCongr_comp]

variable [BraidedCategory C] in
/-- Realization of a tensor product with specified twist counts. -/
lemma homAtOffsets_tensorHom (hL : (β_ L L).hom = 𝟙 _)
    {X X' Y Y' : S} {p p' q q' n m : ℕ}
    (hX : X.level + p = n) (hX' : X'.level + p' = n)
    (hY : Y.level + q = m) (hY' : Y'.level + q' = m)
    (f : X ⟶ X') (g : Y ⟶ Y') :
    homAtOffsets L (tensorOffset L hX hY) (tensorOffset L hX' hY') (tensorHom L f g) =
      (iterateTensorIso L X.obj Y.obj p q).inv ≫
        (homAtOffsets L hX hX' f ⊗ₘ homAtOffsets L hY hY' g) ≫
          (iterateTensorIso L X'.obj Y'.obj p' q').hom := by
  have ep : p = n - X.level := by omega
  have ep' : p' = n - X'.level := by omega
  have eq : q = m - Y.level := by omega
  have eq' : q' = m - Y'.level := by omega
  subst p p' q q'
  have hnX : X.level ≤ n := by omega
  have hnX' : X'.level ≤ n := by omega
  have hmY : Y.level ≤ m := by omega
  have hmY' : Y'.level ≤ m := by omega
  simp only [homAtOffsets, Equiv.trans_apply, Iso.homCongr_apply]
  rw [homEquiv_tensorHom L hL f g hnX hnX' hmY hmY']
  simp only [tensorStageHom, stageTensorIso, stageCoordinateIso, Iso.trans_inv, Iso.trans_hom,
    eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp, Category.comp_id,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- View a numerator map as a stable map between objects with the same denominator. -/
def numeratorHom {X Y : S} (h : X.level = Y.level) (f : X.obj ⟶ Y.obj) : X ⟶ Y :=
  (homAtOffsets L (n := X.level) (p := 0) (q := 0) (by simp)
    (by simpa using h.symm)).symm f

/-- Realizing a numerator map at an offset applies that iterate of the twist functor. -/
lemma homAtOffsets_numeratorHom {X Y : S} (h : X.level = Y.level) {p n : ℕ}
    (hX : X.level + p = n) (hY : Y.level + p = n) (f : X.obj ⟶ Y.obj) :
    homAtOffsets L hX hY (numeratorHom L h f) = (iterate T p).map f := by
  obtain ⟨A, a⟩ := X
  obtain ⟨B, b⟩ := Y
  change a = b at h
  subst b
  have hf : numeratorHom L (X := ⟨A, a⟩) (Y := ⟨B, a⟩) rfl f = (atLevel T a).map f := by
    apply (homAtOffsets L (X := ⟨A, a⟩) (Y := ⟨B, a⟩) (n := a) (p := 0) (q := 0)
      (Nat.add_zero a) (Nat.add_zero a)).injective
    simp only [numeratorHom, Equiv.apply_symm_apply]
    simp only [homAtOffsets, Equiv.trans_apply, Iso.homCongr_apply]
    change f = _ ≫ homEquiv T ((atLevel T a).obj A) ((atLevel T a).obj B)
      a (Nat.le_refl a) (Nat.le_refl a) ((atLevel T a).map f) ≫ _
    rw [homEquiv_atLevel_map_of_le T a a (Nat.le_refl a)]
    have e : iterate T (a - a) = 𝟭 C := by rw [Nat.sub_self, iterate_zero]
    rw [Functor.congr_hom e f]
    simp only [stageCoordinateIso, eqToIso.hom, eqToIso.inv, Functor.id_map, Category.assoc,
      eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [hf]
  simp only [homAtOffsets, Equiv.trans_apply, Iso.homCongr_apply]
  have ha : a ≤ n := by change a + p = n at hX; omega
  change _ ≫ homEquiv T ((atLevel T a).obj A) ((atLevel T a).obj B) n ha ha
    ((atLevel T a).map f) ≫ _ = _
  rw [homEquiv_atLevel_map_of_le T a n ha]
  have e : iterate T (n - a) = iterate T p := congrArg _ (by
    change a + p = n at hX
    omega)
  rw [Functor.congr_hom e f]
  simp only [stageCoordinateIso, eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]

end CategoryTheory.Stabilization
