/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Endofunctor.FixedWords
public import Colib.CategoryTheory.Prespectrum.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Suspension prespectra

Iterating the specified suspension gives the free prespectrum generated
in degree zero. Its adjunction with evaluation retains the original
bonding maps. See Hovey, *Spectra and symmetric spectra in general
model categories*, Definition 1.2, https://arxiv.org/abs/math/0004051.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u

namespace CategoryTheory.SequentialPrespectrum

variable {C : Type u} [Category.{v} C] (S : C ⥤ C)

/-- The suspension prespectrum with its given object in degree zero and
successive suspensions in higher degrees. -/
@[simps]
def suspension : C ⥤ SequentialPrespectrum S where
  obj X :=
    { level := fun n ↦ (Functor.FixedWords.power S n).obj X
      bonding := fun _ ↦ 𝟙 _ }
  map f :=
    { app := fun n ↦ (Functor.FixedWords.power S n).map f
      comm := fun n ↦ by
        change 𝟙 _ ≫ S.map ((Functor.FixedWords.power S n).map f) =
          S.map ((Functor.FixedWords.power S n).map f) ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id] }
  map_id X := Hom.ext (funext fun n ↦ (Functor.FixedWords.power S n).map_id X)
  map_comp f g := Hom.ext (funext fun n ↦ (Functor.FixedWords.power S n).map_comp f g)

variable {S}

private def suspensionDescApp {X : C} {Y : SequentialPrespectrum S} (f : X ⟶ Y.level 0) :
    (n : ℕ) → ((suspension S).obj X).level n ⟶ Y.level n
  | 0 => f
  | n + 1 => S.map (suspensionDescApp f n) ≫ Y.bonding n

/-- Extend the original degree-zero map along the specified bonding maps. -/
@[no_expose]
def suspensionDesc {X : C} {Y : SequentialPrespectrum S} (f : X ⟶ Y.level 0) :
    (suspension S).obj X ⟶ Y where
  app := suspensionDescApp f
  comm n := Category.id_comp (S.map (suspensionDescApp f n) ≫ Y.bonding n)

@[simp]
theorem suspensionDesc_app_zero {X : C} {Y : SequentialPrespectrum S} (f : X ⟶ Y.level 0) :
    (suspensionDesc f).app 0 = f := by
  change suspensionDescApp f 0 = f
  rw [suspensionDescApp]

@[simp]
theorem suspensionDesc_app_succ {X : C} {Y : SequentialPrespectrum S}
    (f : X ⟶ Y.level 0) (n : ℕ) :
    (suspensionDesc f).app (n + 1) = S.map ((suspensionDesc f).app n) ≫ Y.bonding n := by
  change suspensionDescApp f (n + 1) = S.map (suspensionDescApp f n) ≫ Y.bonding n
  rw [suspensionDescApp]

private theorem suspensionDesc_app_eq {X : C} {Y : SequentialPrespectrum S}
    (f : (suspension S).obj X ⟶ Y) :
    ∀ n, (suspensionDesc (X := X) (f.app 0)).app n = f.app n
  | 0 => suspensionDesc_app_zero (X := X) (f.app 0)
  | n + 1 => by
    rw [suspensionDesc_app_succ, suspensionDesc_app_eq f n]
    exact (f.comm n).symm.trans (Category.id_comp (f.app (n + 1)))

/-- Maps out of a suspension prespectrum are determined by the given map
on its degree-zero generator. -/
@[no_expose]
def suspensionHomEquiv (X : C) (Y : SequentialPrespectrum S) :
    ((suspension S).obj X ⟶ Y) ≃ (X ⟶ Y.level 0) where
  toFun f := f.app 0
  invFun := suspensionDesc (X := X)
  left_inv f := Hom.ext (funext (suspensionDesc_app_eq f))
  right_inv f := suspensionDesc_app_zero (X := X) f

private def suspensionAdjunctionCore (S : C ⥤ C) :
    Adjunction.CoreHomEquiv (suspension S) (evaluation 0) where
  homEquiv := suspensionHomEquiv
  homEquiv_naturality_left_symm := fun {X' X Y} f g ↦ by
    let e := suspensionHomEquiv (S := S) X' Y
    let e' := suspensionHomEquiv (S := S) X Y
    apply e.injective
    calc
      e (e.symm (f ≫ g)) = f ≫ g := e.apply_symm_apply _
      _ = e ((suspension S).map f ≫ e'.symm g) := by
        change f ≫ g = f ≫ (suspensionDesc (X := X) g).app 0
        rw [suspensionDesc_app_zero]
  homEquiv_naturality_right := fun _ _ ↦ rfl

/-- The suspension prespectrum functor is left adjoint to evaluation in degree zero. -/
@[no_expose]
def suspensionAdjunction (S : C ⥤ C) : suspension S ⊣ evaluation 0 :=
  Adjunction.mkOfHomEquiv (suspensionAdjunctionCore S)

/-- The adjunction sends a prespectrum map to its actual degree-zero component. -/
theorem suspensionAdjunction_homEquiv {X : C} {Y : SequentialPrespectrum S}
    (f : (suspension S).obj X ⟶ Y) :
    (suspensionAdjunction S).homEquiv X Y f = f.app 0 := by
  change (Adjunction.mkOfHomEquiv (suspensionAdjunctionCore S)).homEquiv X Y f = _
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

end CategoryTheory.SequentialPrespectrum
