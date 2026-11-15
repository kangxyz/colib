/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.FiniteDiagrams

/-! # The inverse twist in finite-stage stabilization -/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

variable {C : Type u} [Category.{v} C] (T : C ⥤ C) [T.Full] [T.Faithful]

/-- Increasing the denominator applies one inverse twist. -/
def inverseTwistObj (X : Stabilization T) : Stabilization T := ⟨X.obj, X.level + 1⟩

/-- Increasing both the stage and the denominator leaves the realized object unchanged. -/
def inverseTwistStageIso (X : Stabilization T) (n : ℕ) :
    stage T (inverseTwistObj T X) (n + 1) ≅ stage T X n :=
  eqToIso (by simp [stage, inverseTwistObj])

private lemma max_succ (a b : ℕ) : max (a + 1) (b + 1) = max a b + 1 := by omega

/-- Increasing both denominators is a bijection on stable Hom sets. -/
def inverseTwistHomEquiv (X Y : Stabilization T) :
    (X ⟶ Y) ≃ (inverseTwistObj T X ⟶ inverseTwistObj T Y) :=
  (eqToIso (show stage T X (max X.level Y.level) =
      stage T (inverseTwistObj T X)
        (max (inverseTwistObj T X).level (inverseTwistObj T Y).level) by
      simp [stage, inverseTwistObj, max_succ])).homCongr
    (eqToIso (show stage T Y (max X.level Y.level) =
      stage T (inverseTwistObj T Y)
        (max (inverseTwistObj T X).level (inverseTwistObj T Y).level) by
      simp [stage, inverseTwistObj, max_succ]))

lemma homEquiv_inverseTwistHomEquiv {X Y : Stabilization T} (f : X ⟶ Y)
    (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n) :
    homEquiv T (inverseTwistObj T X) (inverseTwistObj T Y) (n + 1)
      (Nat.add_le_add_right hX 1) (Nat.add_le_add_right hY 1)
      (inverseTwistHomEquiv T X Y f) =
      (inverseTwistStageIso T X n).hom ≫ homEquiv T X Y n hX hY f ≫
        (inverseTwistStageIso T Y n).inv := by
  let m := max X.level Y.level
  let X' := inverseTwistObj T X
  let Y' := inverseTwistObj T Y
  let m' := max X'.level Y'.level
  let eX : stage T X m = stage T X' m' := by simp [stage, X', Y', m', m, inverseTwistObj, max_succ]
  let eY : stage T Y m = stage T Y' m' := by simp [stage, X', Y', m', m, inverseTwistObj, max_succ]
  have hX' : X'.level ≤ n + 1 := Nat.add_le_add_right hX 1
  have hY' : Y'.level ≤ n + 1 := Nat.add_le_add_right hY 1
  change transition T (X := X') (Y := Y') (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      (max_le hX' hY') (eqToHom eX.symm ≫ f ≫ eqToHom eY) =
    (inverseTwistStageIso T X n).hom ≫ transition T (X := X) (Y := Y)
      (Nat.le_max_left _ _) (Nat.le_max_right _ _) (max_le hX hY) f ≫
      (inverseTwistStageIso T Y n).inv
  have hf : (iterate T (n + 1 - m')).map (f ≫ eqToHom eY) =
      (iterate T (n + 1 - m')).map f ≫ (iterate T (n + 1 - m')).map (eqToHom eY) :=
    (iterate T (n + 1 - m')).map_comp f (eqToHom eY)
  dsimp only [transition, stageIso, inverseTwistStageIso, eqToIso]
  have hfun : iterate T (n - m) = iterate T (n + 1 - m') := by
    congr 1
    dsimp [m, m', X', Y', inverseTwistObj]
    rw [max_succ]
    omega
  rw [Functor.congr_hom hfun f]
  simp only [Functor.map_comp, hf, m', eqToHom_map, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans]

/-- The inverse twist, obtained by increasing each denominator by one. -/
def inverseTwist : Stabilization T ⥤ Stabilization T where
  obj := inverseTwistObj T
  map {X Y} f := inverseTwistHomEquiv T X Y f
  map_id X := by
    have h : (inverseTwistObj T X).level ≤ X.level + 1 := Nat.le_refl _
    apply hom_ext T (X.level + 1) h h
    rw [homEquiv_inverseTwistHomEquiv T _ _ (Nat.le_refl _) (Nat.le_refl _)]
    simp
  map_comp {X Y Z} f g := by
    let n := max (max X.level Y.level) Z.level
    have hX : X.level ≤ n := by dsimp [n]; omega
    have hY : Y.level ≤ n := by dsimp [n]; omega
    have hZ : Z.level ≤ n := by dsimp [n]; omega
    apply hom_ext T (n + 1) (Nat.add_le_add_right hX 1) (Nat.add_le_add_right hZ 1)
    rw [homEquiv_comp T _ _ (n + 1) (Nat.add_le_add_right hX 1)
      (Nat.add_le_add_right hY 1) (Nat.add_le_add_right hZ 1)]
    simp only [homEquiv_inverseTwistHomEquiv T _ n hX hY,
      homEquiv_inverseTwistHomEquiv T _ n hY hZ,
      homEquiv_inverseTwistHomEquiv T _ n hX hZ, homEquiv_comp T _ _ n hX hY hZ]
    simp

instance inverseTwist_full : (inverseTwist T).Full where
  map_surjective := (inverseTwistHomEquiv T _ _).surjective

instance inverseTwist_faithful : (inverseTwist T).Faithful where
  map_injective {X Y} := by
    intro f g h
    exact (inverseTwistHomEquiv T X Y).injective h

/-- Applying `T` before adding an inverse twist recovers the original object. -/
def inverseTwistObjIso (X : Stabilization T) :
    (inverseTwist T).obj ⟨T.obj X.obj, X.level⟩ ≅ X :=
  isoOfStage T _ X (X.level + 1) (Nat.le_refl _) (Nat.le_succ _) (eqToIso (by
    simp [inverseTwist, inverseTwistObj, stage, iterate]))

instance inverseTwist_essSurj : (inverseTwist T).EssSurj where
  mem_essImage X := ⟨⟨T.obj X.obj, X.level⟩, ⟨inverseTwistObjIso T X⟩⟩

instance inverseTwist_isEquivalence : (inverseTwist T).IsEquivalence where

/-- Formal inversion turns the inverse twist into an autoequivalence. -/
def inverseTwistEquivalence : Stabilization T ≌ Stabilization T :=
  (inverseTwist T).asEquivalence

/-- The autoequivalence inverse to increasing the denominator. -/
def twistEquivalence : Stabilization T ≌ Stabilization T :=
  (inverseTwistEquivalence T).symm

end CategoryTheory.Stabilization
