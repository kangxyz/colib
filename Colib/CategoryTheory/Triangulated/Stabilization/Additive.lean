/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Additive structure on finite-twist stabilization -/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

open Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (T : C ⥤ C) [T.Full] [T.Faithful] [T.Additive]

instance iterate_additive (n : ℕ) : (iterate T n).Additive := by
  induction n with
  | zero => change (𝟭 C).Additive; infer_instance
  | succ n ih => change (iterate T n ⋙ T).Additive; infer_instance

instance homAddCommGroup (X Y : Stabilization T) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup
    (stage T X (max X.level Y.level) ⟶ stage T Y (max X.level Y.level)))

omit [T.Full] [T.Faithful] in
@[simp] lemma transition_add {X Y : Stabilization T} {m n : ℕ}
    (hX : X.level ≤ m) (hY : Y.level ≤ m) (h : m ≤ n)
    (f g : stage T X m ⟶ stage T Y m) :
    transition T hX hY h (f + g) = transition T hX hY h f + transition T hX hY h g := by
  simp [transition, Preadditive.comp_add]

@[simp] lemma homEquiv_add {X Y : Stabilization T} (n : ℕ)
    (hX : X.level ≤ n) (hY : Y.level ≤ n) (f g : X ⟶ Y) :
    homEquiv T X Y n hX hY (f + g) =
      homEquiv T X Y n hX hY f + homEquiv T X Y n hX hY g :=
  transition_add T _ _ _ _ _

instance : Preadditive (Stabilization T) where
  homGroup := homAddCommGroup T
  add_comp X Y Z f f' g := by
    let n := max (max X.level Y.level) Z.level
    have hX : X.level ≤ n := by dsimp [n]; omega
    have hY : Y.level ≤ n := by dsimp [n]; omega
    have hZ : Z.level ≤ n := by dsimp [n]; omega
    apply hom_ext T n hX hZ
    simp only [homEquiv_add, homEquiv_comp T _ _ n hX hY hZ, Preadditive.add_comp]
  comp_add X Y Z f g g' := by
    let n := max (max X.level Y.level) Z.level
    have hX : X.level ≤ n := by dsimp [n]; omega
    have hY : Y.level ≤ n := by dsimp [n]; omega
    have hZ : Z.level ≤ n := by dsimp [n]; omega
    apply hom_ext T n hX hZ
    simp only [homEquiv_add, homEquiv_comp T _ _ n hX hY hZ, Preadditive.comp_add]

/-- Common-stage realization is an isomorphism of abelian groups. -/
def homAddEquiv (X Y : Stabilization T) (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n) :
    (X ⟶ Y) ≃+ (stage T X n ⟶ stage T Y n) where
  toEquiv := homEquiv T X Y n hX hY
  map_add' := homEquiv_add T n hX hY

@[simp] lemma homEquiv_zero (X Y : Stabilization T) (n : ℕ)
    (hX : X.level ≤ n) (hY : Y.level ≤ n) :
    homEquiv T X Y n hX hY 0 = 0 := (homAddEquiv T X Y n hX hY).map_zero

@[simp] lemma homEquiv_neg {X Y : Stabilization T} (n : ℕ)
    (hX : X.level ≤ n) (hY : Y.level ≤ n) (f : X ⟶ Y) :
    homEquiv T X Y n hX hY (-f) = -homEquiv T X Y n hX hY f :=
  (homAddEquiv T X Y n hX hY).map_neg f

instance atLevel_additive (n : ℕ) : (atLevel T n).Additive where
  map_add {X Y f g} := by
    let eX : X ≅ stage T (⟨X, n⟩ : Stabilization T) (max n n) :=
      eqToIso (by simp [stage])
    let eY : Y ≅ stage T (⟨Y, n⟩ : Stabilization T) (max n n) :=
      eqToIso (by simp [stage])
    change eX.inv ≫ (f + g) ≫ eY.hom =
      (eX.inv ≫ f ≫ eY.hom) + (eX.inv ≫ g ≫ eY.hom)
    simp only [Preadditive.add_comp, Preadditive.comp_add]

instance [HasZeroObject C] : HasZeroObject (Stabilization T) :=
  (inclusion T).hasZeroObject_of_additive

end CategoryTheory.Stabilization
