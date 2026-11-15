/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Data.Nat.Basic

/-! # Finite stages for inversion of a fully faithful endofunctor

An object is a pair `(A, a)` representing `T⁻ᵃ A`. At a common level `n`, it is
represented by `T^(n-a) A`. Transition between common levels is bijective on
morphisms. The eventual stabilization uses the maximum of the two denominators
as its actual Hom set; it does not take a colimit of Hom sets.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- An object of the formal inversion of an endofunctor: `obj` with `level` inverse twists. -/
structure Stabilization (T : C ⥤ C) where
  /-- The object before applying inverse twists. -/
  obj : C
  /-- The number of inverse twists. -/
  level : ℕ

namespace Stabilization

variable (T : C ⥤ C)

/-- The chosen finite iterate of the endofunctor. -/
def iterate : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => iterate n ⋙ T

@[simp] lemma iterate_zero : iterate T 0 = 𝟭 C := rfl

@[simp] lemma iterate_succ (n : ℕ) : iterate T (n + 1) = iterate T n ⋙ T := rfl

lemma iterate_add (a b : ℕ) : iterate T (a + b) = iterate T a ⋙ iterate T b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [Nat.add_succ, iterate_succ, ih, iterate_succ]; rfl

instance [T.Full] (n : ℕ) : (iterate T n).Full := by
  induction n with
  | zero => change (𝟭 C).Full; infer_instance
  | succ n ih => change (iterate T n ⋙ T).Full; infer_instance

instance [T.Faithful] (n : ℕ) : (iterate T n).Faithful := by
  induction n with
  | zero => change (𝟭 C).Faithful; infer_instance
  | succ n ih => change (iterate T n ⋙ T).Faithful; infer_instance

/-- Realization of a formal inverse twist at level `n`; used only for `X.level ≤ n`. -/
def stage (X : Stabilization T) (n : ℕ) : C :=
  (iterate T (n - X.level)).obj X.obj

/-- The canonical comparison obtained by adding twists to a finite stage. -/
def stageIso (X : Stabilization T) {m n : ℕ} (hX : X.level ≤ m) (h : m ≤ n) :
    (iterate T (n - m)).obj (stage T X m) ≅ stage T X n :=
  eqToIso (by
    dsimp only [stage]
    rw [← Functor.comp_obj, ← iterate_add]
    congr 2
    omega)

/-- Move a morphism from one common level to a larger common level. -/
def transition {X Y : Stabilization T} {m n : ℕ}
    (hX : X.level ≤ m) (hY : Y.level ≤ m) (h : m ≤ n)
    (f : stage T X m ⟶ stage T Y m) : stage T X n ⟶ stage T Y n :=
  (stageIso T X hX h).inv ≫ (iterate T (n - m)).map f ≫ (stageIso T Y hY h).hom

@[simp] lemma transition_refl {X Y : Stabilization T} {m : ℕ}
    (hX : X.level ≤ m) (hY : Y.level ≤ m) (f : stage T X m ⟶ stage T Y m) :
    transition T hX hY (Nat.le_refl m) f = f := by
  dsimp only [transition, stageIso, eqToIso]
  have hfun : iterate T (m - m) = 𝟭 C := by rw [Nat.sub_self, iterate_zero]
  rw [Functor.congr_hom hfun f]
  simp only [Functor.id_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp, Category.comp_id]

@[simp] lemma transition_id {X : Stabilization T} {m n : ℕ}
    (hX : X.level ≤ m) (h : m ≤ n) :
    transition T hX hX h (𝟙 (stage T X m)) = 𝟙 (stage T X n) := by
  simp [transition]

lemma transition_comp {X Y Z : Stabilization T} {m n : ℕ}
    (hX : X.level ≤ m) (hY : Y.level ≤ m) (hZ : Z.level ≤ m) (h : m ≤ n)
    (f : stage T X m ⟶ stage T Y m) (g : stage T Y m ⟶ stage T Z m) :
    transition T hX hZ h (f ≫ g) =
      transition T hX hY h f ≫ transition T hY hZ h g := by
  simp [transition]

lemma transition_trans {X Y : Stabilization T} {l m n : ℕ}
    (hX : X.level ≤ l) (hY : Y.level ≤ l) (hlm : l ≤ m) (hmn : m ≤ n)
    (f : stage T X l ⟶ stage T Y l) :
    transition T (Nat.le_trans hX hlm) (Nat.le_trans hY hlm) hmn (transition T hX hY hlm f) =
      transition T hX hY (Nat.le_trans hlm hmn) f := by
  have hsub : n - l = (m - l) + (n - m) := by omega
  dsimp only [transition, stageIso, eqToIso]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans]
  have hfun : iterate T (n - l) = iterate T (m - l) ⋙ iterate T (n - m) :=
    (congrArg (iterate T) hsub).trans (iterate_add T (m - l) (n - m))
  rw [Functor.congr_hom hfun f]
  simp only [Functor.comp_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

/-- Full faithfulness makes every finite stage transition an equivalence of Hom sets. -/
def transitionEquiv [T.Full] [T.Faithful] {X Y : Stabilization T} {m n : ℕ}
    (hX : X.level ≤ m) (hY : Y.level ≤ m) (h : m ≤ n) :
    (stage T X m ⟶ stage T Y m) ≃ (stage T X n ⟶ stage T Y n) :=
  (Functor.FullyFaithful.ofFullyFaithful (iterate T (n - m))).homEquiv.trans
    ((stageIso T X hX h).homCongr (stageIso T Y hY h))

@[simp] lemma transitionEquiv_apply [T.Full] [T.Faithful]
    {X Y : Stabilization T} {m n : ℕ}
    (hX : X.level ≤ m) (hY : Y.level ≤ m) (h : m ≤ n)
    (f : stage T X m ⟶ stage T Y m) :
    transitionEquiv T hX hY h f = transition T hX hY h f := rfl

lemma transition_injective [T.Full] [T.Faithful]
    {X Y : Stabilization T} {m n : ℕ}
    (hX : X.level ≤ m) (hY : Y.level ≤ m) (h : m ≤ n) :
    Function.Injective (transition T (X := X) (Y := Y) hX hY h) :=
  (transitionEquiv T hX hY h).injective

end Stabilization

end CategoryTheory
