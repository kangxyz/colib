/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Coordinates
public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Coherence

/-! # Stable associator, unitors and symmetry

The structural isomorphisms are the numerator isomorphisms at equal
denominators. At arbitrary stages they are conjugates of the structural
isomorphisms of the realizations by the tensor comparisons.
-/

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

/-- Regard an isomorphism of numerators as a stable isomorphism at equal denominators. -/
def numeratorIso {X Y : S} (h : X.level = Y.level) (e : X.obj ≅ Y.obj) : X ≅ Y where
  hom := numeratorHom L h e.hom
  inv := numeratorHom L h.symm e.inv
  hom_inv_id := by
    have hX : X.level + 0 = X.level := Nat.add_zero _
    have hY : Y.level + 0 = X.level := (Nat.add_zero _).trans h.symm
    apply (homAtOffsets L hX hX).injective
    rw [homAtOffsets_comp L hX hY hX, homAtOffsets_numeratorHom L h hX hY,
      homAtOffsets_numeratorHom L h.symm hY hX, homAtOffsets_id]
    exact e.hom_inv_id
  inv_hom_id := by
    have hX : X.level + 0 = Y.level := (Nat.add_zero _).trans h
    have hY : Y.level + 0 = Y.level := Nat.add_zero _
    apply (homAtOffsets L hY hY).injective
    rw [homAtOffsets_comp L hY hX hY, homAtOffsets_numeratorHom L h.symm hY hX,
      homAtOffsets_numeratorHom L h hX hY, homAtOffsets_id]
    exact e.inv_hom_id

/-- The stable tensor unit has denominator zero. -/
def tensorUnit : S := ⟨𝟙_ C, 0⟩

omit [(tensorRight L).Full] [(tensorRight L).Faithful] in
/-- The tensor unit has no inverse twist. -/
@[simp] lemma level_tensorUnit : (tensorUnit L).level = 0 := rfl

/-- The associator of the stable tensor product. -/
def tensorAssociator (X Y Z : S) : ((X ⊗ₛ Y) ⊗ₛ Z) ≅ (X ⊗ₛ (Y ⊗ₛ Z)) :=
  numeratorIso L (Nat.add_assoc X.level Y.level Z.level) (α_ X.obj Y.obj Z.obj)

/-- The left unitor of the stable tensor product. -/
def tensorLeftUnitor (X : S) : (tensorUnit L ⊗ₛ X) ≅ X :=
  numeratorIso L (Nat.zero_add X.level) (λ_ X.obj)

/-- The right unitor of the stable tensor product. -/
def tensorRightUnitor (X : S) : (X ⊗ₛ tensorUnit L) ≅ X :=
  numeratorIso L (Nat.add_zero X.level) (ρ_ X.obj)

section Braided

variable [BraidedCategory C]

/-- The braiding of the stable tensor product. -/
def tensorBraiding (X Y : S) : (X ⊗ₛ Y) ≅ (Y ⊗ₛ X) :=
  numeratorIso L (Nat.add_comm X.level Y.level) (β_ X.obj Y.obj)

omit [BraidedCategory C] in
private lemma homAtOffsets_numeratorHom_reindex
    {X Y : S} {p q n : ℕ} (h : X.level = Y.level)
    (hX : X.level + p = n) (hY : Y.level + q = n) (e : p = q) (f : X.obj ⟶ Y.obj) :
    homAtOffsets L hX hY (numeratorHom L h f) =
      (iterate T p).map f ≫ eqToHom (congrArg (fun k => I k Y.obj) e) := by
  subst q
  simp only [eqToHom_refl, Category.comp_id]
  exact homAtOffsets_numeratorHom L h hX hY f

/-- At any stage the associator is the corresponding conjugated associator. -/
lemma homAtOffsets_tensorAssociator (hL : (β_ L L).hom = 𝟙 _) {X Y Z : S}
    {p q r n m k : ℕ} (hX : X.level + p = n) (hY : Y.level + q = m)
    (hZ : Z.level + r = k) :
    homAtOffsets L
        (tensorOffset L (tensorOffset L hX hY) hZ)
        ((tensorOffset L hX (tensorOffset L hY hZ)).trans (Nat.add_assoc n m k).symm)
        (tensorAssociator L X Y Z).hom =
      (P (X.obj ⊗ Y.obj) Z.obj (p + q) r).inv ≫
        ((P X.obj Y.obj p q).inv ▷ I r Z.obj) ≫ (α_ (I p X.obj) (I q Y.obj) (I r Z.obj)).hom ≫
        (I p X.obj ◁ (P Y.obj Z.obj q r).hom) ≫ (P X.obj (Y.obj ⊗ Z.obj) p (q + r)).hom := by
  rw [tensorAssociator, numeratorIso,
    homAtOffsets_numeratorHom_reindex L _ _ _ (Nat.add_assoc p q r)]
  rw [← iterateTensorIso_associator L hL]
  simp only [Iso.inv_hom_id_assoc, inv_hom_whiskerRight_assoc]

/-- At any stage the left unitor is the corresponding conjugated left unitor. -/
lemma homAtOffsets_tensorLeftUnitor {X : S} {p n : ℕ} (hX : X.level + p = n) :
    homAtOffsets L (tensorOffset L (X := tensorUnit L) (p := 0) (n := 0) (level_tensorUnit L) hX)
        (hX.trans (Nat.zero_add n).symm) (tensorLeftUnitor L X).hom =
      (P (𝟙_ C) X.obj 0 p).inv ≫ (λ_ (I p X.obj)).hom := by
  rw [tensorLeftUnitor, numeratorIso, homAtOffsets_numeratorHom_reindex L _ _ _ (Nat.zero_add p),
    ← iterateTensorIso_leftUnitor L, Iso.inv_hom_id_assoc]

/-- At any stage the right unitor is the corresponding conjugated right unitor. -/
lemma homAtOffsets_tensorRightUnitor (hL : (β_ L L).hom = 𝟙 _) {X : S} {p n : ℕ}
    (hX : X.level + p = n) :
    homAtOffsets L (tensorOffset L (Y := tensorUnit L) (q := 0) (m := 0) hX (level_tensorUnit L))
        hX (tensorRightUnitor L X).hom =
      (P X.obj (𝟙_ C) p 0).inv ≫ (ρ_ (I p X.obj)).hom := by
  have h : (X ⊗ₛ tensorUnit L).level = X.level := by simp
  let f : (X ⊗ₛ tensorUnit L).obj ⟶ X.obj := (ρ_ X.obj).hom
  have hs : (X ⊗ₛ tensorUnit L).level + p = n := by simpa [h] using hX
  calc
    _ = (iterate T p).map f := homAtOffsets_numeratorHom L h hs hX f
    _ = _ := by
      have e := iterateTensorIso_rightUnitor L hL X.obj p
      exact (Iso.inv_hom_id_assoc (P X.obj (𝟙_ C) p 0) ((iterate T p).map f)).symm.trans
        (congrArg (fun g => (P X.obj (𝟙_ C) p 0).inv ≫ g) e)

end Braided

variable [SymmetricCategory C]

/-- At any stage the braiding is the corresponding conjugated braiding. -/
lemma homAtOffsets_tensorBraiding (hL : (β_ L L).hom = 𝟙 _) {X Y : S}
    {p q n m : ℕ} (hX : X.level + p = n) (hY : Y.level + q = m) :
    homAtOffsets L (tensorOffset L hX hY) ((tensorOffset L hY hX).trans (Nat.add_comm m n))
        (tensorBraiding L X Y).hom =
      (P X.obj Y.obj p q).inv ≫ (β_ (I p X.obj) (I q Y.obj)).hom ≫ (P Y.obj X.obj q p).hom := by
  rw [tensorBraiding, numeratorIso, homAtOffsets_numeratorHom_reindex L _ _ _ (Nat.add_comm p q),
    ← iterateTensorIso_braiding L hL, Iso.inv_hom_id_assoc]

end CategoryTheory.Stabilization
