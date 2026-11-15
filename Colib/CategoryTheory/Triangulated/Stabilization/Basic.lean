/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Stages

/-! # The category obtained by inverting a fully faithful endofunctor

Morphisms are computed at the maximum of the two inverse-twist denominators.
Composition is computed at a common stage and brought back by full faithfulness.
The common-stage formulas prove all category axioms and independence of the
stage used in a calculation.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

variable {C : Type u} [Category.{v} C] (T : C ⥤ C) [T.Full] [T.Faithful]

/-- Morphisms at the least common stage. -/
def Hom (X Y : Stabilization T) : Type v :=
  stage T X (max X.level Y.level) ⟶ stage T Y (max X.level Y.level)

namespace Hom

variable {T} {W X Y Z : Stabilization T}

/-- Express a stable morphism at any common stage. -/
def toStage (f : Hom T X Y) (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n) :
    stage T X n ⟶ stage T Y n :=
  transition T (Nat.le_max_left _ _) (Nat.le_max_right _ _) (max_le hX hY) f

omit [T.Full] [T.Faithful] in
@[simp] lemma toStage_max (f : Hom T X Y) :
    toStage f (max X.level Y.level) (Nat.le_max_left _ _) (Nat.le_max_right _ _) = f :=
  transition_refl T _ _ f

/-- Regard a map at a common stage as a stable morphism. -/
def ofStage (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n)
    (f : stage T X n ⟶ stage T Y n) : Hom T X Y :=
  (transitionEquiv T (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    (max_le hX hY)).symm f

@[simp] lemma toStage_ofStage (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n)
    (f : stage T X n ⟶ stage T Y n) :
    toStage (ofStage n hX hY f) n hX hY = f :=
  (transitionEquiv T (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    (max_le hX hY)).apply_symm_apply f

@[simp] lemma ofStage_toStage (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n)
    (f : Hom T X Y) : ofStage n hX hY (toStage f n hX hY) = f :=
  (transitionEquiv T (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    (max_le hX hY)).symm_apply_apply f

lemma toStage_injective (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n) :
    Function.Injective (fun f : Hom T X Y => toStage f n hX hY) :=
  transition_injective T _ _ _

omit [T.Full] [T.Faithful] in
lemma toStage_trans (f : Hom T X Y) {m n : ℕ}
    (hX : X.level ≤ m) (hY : Y.level ≤ m) (h : m ≤ n) :
    transition T hX hY h (toStage f m hX hY) =
      toStage f n (Nat.le_trans hX h) (Nat.le_trans hY h) :=
  transition_trans T _ _ _ _ _

lemma toStage_ofStage_of_le {m n : ℕ} (hX : X.level ≤ m) (hY : Y.level ≤ m)
    (h : m ≤ n) (f : stage T X m ⟶ stage T Y m) :
    toStage (ofStage m hX hY f) n (Nat.le_trans hX h) (Nat.le_trans hY h) =
      transition T hX hY h f := by
  rw [← toStage_trans, toStage_ofStage]

/-- The identity, at the least common stage. -/
def id (X : Stabilization T) : Hom T X X := 𝟙 _

omit [T.Full] [T.Faithful] in
@[simp] lemma toStage_id (X : Stabilization T) (n : ℕ) (hX : X.level ≤ n) :
    toStage (id X) n hX hX = 𝟙 (stage T X n) :=
  transition_id T _ _

/-- Composition after clearing the three denominators. -/
def comp (f : Hom T X Y) (g : Hom T Y Z) : Hom T X Z :=
  let n := max (max X.level Y.level) Z.level
  ofStage n (by dsimp [n]; omega) (by dsimp [n]; omega)
    (toStage f n (by dsimp [n]; omega) (by dsimp [n]; omega) ≫
      toStage g n (by dsimp [n]; omega) (by dsimp [n]; omega))

lemma toStage_comp (f : Hom T X Y) (g : Hom T Y Z) (n : ℕ)
    (hX : X.level ≤ n) (hY : Y.level ≤ n) (hZ : Z.level ≤ n) :
    toStage (comp f g) n hX hZ = toStage f n hX hY ≫ toStage g n hY hZ := by
  let m := max (max X.level Y.level) Z.level
  let p := max m n
  have hm : m ≤ p := Nat.le_max_left _ _
  have hn : n ≤ p := Nat.le_max_right _ _
  have hmX : X.level ≤ m := by dsimp [m]; omega
  have hmY : Y.level ≤ m := by dsimp [m]; omega
  have hmZ : Z.level ≤ m := by dsimp [m]; omega
  apply transition_injective T hX hZ hn
  rw [toStage_trans _ hX hZ hn, transition_comp T hX hY hZ hn,
    toStage_trans f hX hY hn, toStage_trans g hY hZ hn]
  dsimp only [comp]
  rw [toStage_ofStage_of_le hmX hmZ hm, transition_comp T hmX hmY hmZ hm,
    toStage_trans f hmX hmY hm, toStage_trans g hmY hmZ hm]

lemma id_comp (f : Hom T X Y) : comp (id X) f = f := by
  apply toStage_injective (max X.level Y.level) (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  dsimp only
  rw [toStage_comp _ _ _ (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    (Nat.le_max_right _ _), toStage_id, Category.id_comp]

lemma comp_id (f : Hom T X Y) : comp f (id Y) = f := by
  apply toStage_injective (max X.level Y.level) (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  dsimp only
  rw [toStage_comp _ _ _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    (Nat.le_max_right _ _), toStage_id, Category.comp_id]

lemma assoc (f : Hom T W X) (g : Hom T X Y) (h : Hom T Y Z) :
    comp (comp f g) h = comp f (comp g h) := by
  let n := max (max W.level X.level) (max Y.level Z.level)
  have hW : W.level ≤ n := by dsimp [n]; omega
  have hX : X.level ≤ n := by dsimp [n]; omega
  have hY : Y.level ≤ n := by dsimp [n]; omega
  have hZ : Z.level ≤ n := by dsimp [n]; omega
  apply toStage_injective n hW hZ
  dsimp only
  rw [toStage_comp _ _ n hW hY hZ, toStage_comp _ _ n hW hX hY,
    toStage_comp _ _ n hW hX hZ, toStage_comp _ _ n hX hY hZ, Category.assoc]

end Hom

instance : Category.{v} (Stabilization T) where
  Hom := Hom T
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- A stable Hom set is exactly the Hom set at any common finite level. -/
def homEquiv (X Y : Stabilization T) (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n) :
    (X ⟶ Y) ≃ (stage T X n ⟶ stage T Y n) where
  toFun f := Hom.toStage f n hX hY
  invFun f := Hom.ofStage n hX hY f
  left_inv := Hom.ofStage_toStage n hX hY
  right_inv := Hom.toStage_ofStage n hX hY

@[simp] lemma homEquiv_id (X : Stabilization T) (n : ℕ) (hX : X.level ≤ n) :
    homEquiv T X X n hX hX (𝟙 X) = 𝟙 (stage T X n) := Hom.toStage_id X n hX

lemma homEquiv_comp {X Y Z : Stabilization T} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n) (hZ : Z.level ≤ n) :
    homEquiv T X Z n hX hZ (f ≫ g) =
      homEquiv T X Y n hX hY f ≫ homEquiv T Y Z n hY hZ g :=
  Hom.toStage_comp f g n hX hY hZ

@[simp] lemma homEquiv_max (X Y : Stabilization T) (f : X ⟶ Y) :
    homEquiv T X Y (max X.level Y.level) (Nat.le_max_left _ _) (Nat.le_max_right _ _) f = f :=
  Hom.toStage_max f

/-- Equality, and hence every commutative finite diagram, can be tested at a common stage. -/
lemma hom_ext {X Y : Stabilization T} (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n)
    {f g : X ⟶ Y} (h : homEquiv T X Y n hX hY f = homEquiv T X Y n hX hY g) : f = g :=
  (homEquiv T X Y n hX hY).injective h

/-- The Hom equivalence between two objects with the same denominator. -/
def atLevelHomEquiv (n : ℕ) (A B : C) : (A ⟶ B) ≃ ((⟨A, n⟩ : Stabilization T) ⟶ ⟨B, n⟩) :=
  (eqToIso (show A = stage T ⟨A, n⟩ (max n n) by simp [stage])).homCongr
    (eqToIso (show B = stage T ⟨B, n⟩ (max n n) by simp [stage]))

/-- The fully faithful inclusion of the category at a specified finite inverse twist. -/
def atLevel (n : ℕ) : C ⥤ Stabilization T where
  obj A := ⟨A, n⟩
  map f := atLevelHomEquiv T n _ _ f
  map_id A := by
    let e : A ≅ stage T (⟨A, n⟩ : Stabilization T) (max n n) :=
      eqToIso (by simp [stage])
    change e.inv ≫ (𝟙 A) ≫ e.hom = 𝟙 _
    simp
  map_comp {A B D} f g := by
    apply hom_ext T (max n n) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    rw [homEquiv_comp T _ _ (max n n) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
      (Nat.le_max_left _ _)]
    rw [homEquiv_max, homEquiv_max, homEquiv_max]
    exact Iso.homCongr_comp _ _ _ f g

instance atLevel_full (n : ℕ) : (atLevel T n).Full where
  map_surjective := (atLevelHomEquiv T n _ _).surjective

instance atLevel_faithful (n : ℕ) : (atLevel T n).Faithful where
  map_injective {A B} := by
    intro f g h
    exact (atLevelHomEquiv T n A B).injective h

/-- The original category sits fully faithfully at denominator zero. -/
abbrev inclusion : C ⥤ Stabilization T := atLevel T 0

end CategoryTheory.Stabilization
