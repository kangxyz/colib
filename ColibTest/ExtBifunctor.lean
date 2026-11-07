/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Algebra.Homology.DerivedCategory.Ext.Bifunctor.Linear

/-! Regression examples for the unchanged native external Ext product and its signs. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.Functor
open scoped TensorProduct

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃ r

section Additive

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w₃} E]
  (F : C ⥤ D ⥤ E) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ X, PreservesFiniteLimits (F.obj X)] [∀ X, PreservesFiniteColimits (F.obj X)]
  [∀ Y, PreservesFiniteLimits (F.flip.obj Y)]
  [∀ Y, PreservesFiniteColimits (F.flip.obj Y)]

local instance (Y : D) : (F.flip.obj Y).Additive := { }

example {X₀ X₁ : C} {Y₀ Y₁ : D}
    (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) :
    extBifunctor F (Ext.mk₀ f) (Ext.mk₀ g) (zero_add 0) =
      Ext.mk₀ ((F.map f).app Y₀ ≫ (F.obj X₁).map g) :=
  F.extBifunctor_mk₀_mk₀ f g

example {X₀ X₁ : C} {Y₀ Y₁ : D} {q : ℕ}
    (f : X₀ ⟶ X₁) (y : Ext.{w₂} Y₀ Y₁ q) :
    extBifunctor F (Ext.mk₀ f) y (zero_add q) =
      (y.mapExactFunctor (F.obj X₀)).comp (Ext.mk₀ ((F.map f).app Y₁)) (add_zero q) :=
  F.extBifunctor_mk₀_left f y

example {X₀ X₁ : C} {Y₀ Y₁ : D} {p : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (g : Y₀ ⟶ Y₁) :
    extBifunctor F x (Ext.mk₀ g) (add_zero p) =
      (Ext.mk₀ ((F.obj X₀).map g)).comp
        (x.mapExactFunctor (F.flip.obj Y₁)) (zero_add p) :=
  F.extBifunctor_mk₀_right x g

example {S : ShortComplex C} {T : ShortComplex D}
    (hS : S.ShortExact) (hT : T.ShortExact) :
    extBifunctor F hS.extClass hT.extClass (show 1 + 1 = 2 from rfl) =
      -((hT.extClass.mapExactFunctor (F.obj S.X₃)).comp
        (hS.extClass.mapExactFunctor (F.flip.obj T.X₁)) (show 1 + 1 = 2 from rfl)) :=
  F.extBifunctor_extClass_extClass hS hT

example {X₀ X₁ : C} {Y₀ Y₁ : D} {p q n : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) (h : p + q = n) :
    extBifunctor F x y h = ((-1 : ℤ) ^ (p * q)) •
      (y.mapExactFunctor (F.obj X₀)).comp
        (x.mapExactFunctor (F.flip.obj Y₁)) ((Nat.add_comm q p).trans h) :=
  F.extBifunctor_comm x y h

example {X' X₀ X₁ : C} {Y₀ Y₁ : D} {p q n : ℕ}
    (f : X' ⟶ X₀) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q)
    (h : p + q = n) :
    extBifunctor F ((Ext.mk₀ f).comp x (zero_add p)) y h =
      (Ext.mk₀ ((F.map f).app Y₀)).comp (extBifunctor F x y h) (zero_add n) :=
  F.extBifunctor_mk₀_comp_left f x y h

example {X₀ X₁ X' : C} {Y₀ Y₁ : D} {p q n : ℕ}
    (f : X₁ ⟶ X') (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q)
    (h : p + q = n) :
    extBifunctor F (x.comp (Ext.mk₀ f) (add_zero p)) y h =
      (extBifunctor F x y h).comp (Ext.mk₀ ((F.map f).app Y₁)) (add_zero n) :=
  F.extBifunctor_comp_mk₀_left f x y h

example {X₀ X₁ : C} {Y' Y₀ Y₁ : D} {p q n : ℕ}
    (g : Y' ⟶ Y₀) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q)
    (h : p + q = n) :
    extBifunctor F x ((Ext.mk₀ g).comp y (zero_add q)) h =
      (Ext.mk₀ ((F.obj X₀).map g)).comp (extBifunctor F x y h) (zero_add n) :=
  F.extBifunctor_mk₀_comp_right g x y h

example {X₀ X₁ : C} {Y₀ Y₁ Y' : D} {p q n : ℕ}
    (g : Y₁ ⟶ Y') (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q)
    (h : p + q = n) :
    extBifunctor F x (y.comp (Ext.mk₀ g) (add_zero q)) h =
      (extBifunctor F x y h).comp (Ext.mk₀ ((F.obj X₁).map g)) (add_zero n) :=
  F.extBifunctor_comp_mk₀_right g x y h

example
    (G : C ⥤ D ⥤ E) [G.Additive] [∀ X, (G.obj X).Additive]
    [∀ X, PreservesFiniteLimits (G.obj X)] [∀ X, PreservesFiniteColimits (G.obj X)]
    [∀ Y, PreservesFiniteLimits (G.flip.obj Y)]
    [∀ Y, PreservesFiniteColimits (G.flip.obj Y)]
    (τ : F ⟶ G) {X₀ X₁ : C} {Y₀ Y₁ : D} {p q n : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) (h : p + q = n) :
    (extBifunctor F x y h).comp (Ext.mk₀ ((τ.app X₁).app Y₁)) (add_zero n) =
      (Ext.mk₀ ((τ.app X₀).app Y₀)).comp (extBifunctor G x y h) (zero_add n) :=
  F.extBifunctor_natTrans G τ x y h

example {S : ShortComplex C} (hS : S.ShortExact)
    {X₁ : C} {Y₀ Y₁ : D} {p p' q n n' : ℕ}
    (x : Ext.{w₁} S.X₁ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q)
    (hp : 1 + p = p') (h : p + q = n) (h' : p' + q = n') :
    extBifunctor F (hS.extClass.comp x hp) y h' =
      (hS.map_of_exact (F.flip.obj Y₀)).extClass.comp
        (extBifunctor F x y h) (by omega) :=
  F.extBifunctor_extClass_comp_left hS x y hp h h'

example {T : ShortComplex D} (hT : T.ShortExact)
    {X₀ X₁ : C} {Y₁ : D} {p q q' n n' : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} T.X₁ Y₁ q)
    (hq : 1 + q = q') (h : p + q = n) (h' : p + q' = n') :
    extBifunctor F x (hT.extClass.comp y hq) h' = ((-1 : ℤ) ^ p) •
      (hT.map_of_exact (F.obj X₀)).extClass.comp (extBifunctor F x y h) (by omega) :=
  F.extBifunctor_extClass_comp_right hT x y hq h h'

example {S : ShortComplex C} (hS : S.ShortExact)
    {X₁ : C} {Y₀ Y₁ : D} {p p' q n n' : ℕ}
    (x : Ext.{w₁} S.X₁ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q)
    (hp : p + 1 = p') (h : p + q = n) (h' : p' + q = n') :
    extBifunctor F (Ext.δ hS p p' hp x) y h' = ((-1 : ℤ) ^ q) •
      Ext.δ (hS.map_of_exact (F.flip.obj Y₀)) n n' (by omega) (extBifunctor F x y h) :=
  F.extBifunctor_δ_left hS x y hp h h'

example {T : ShortComplex D} (hT : T.ShortExact)
    {X₀ X₁ : C} {Y₁ : D} {p q q' n n' : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} T.X₁ Y₁ q)
    (hq : q + 1 = q') (h : p + q = n) (h' : p + q' = n') :
    extBifunctor F x (Ext.δ hT q q' hq y) h' =
      Ext.δ (hT.map_of_exact (F.obj X₀)) n n' (by omega) (extBifunctor F x y h) :=
  F.extBifunctor_δ_right hT x y hq h h'

end Additive

section Linear

variable {R : Type r} [CommRing R]
  {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C] [CategoryTheory.Linear R C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D] [CategoryTheory.Linear R D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w₃} E] [CategoryTheory.Linear R E]
  (F : C ⥤ D ⥤ E) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ X, PreservesFiniteLimits (F.obj X)] [∀ X, PreservesFiniteColimits (F.obj X)]
  [∀ Y, PreservesFiniteLimits (F.flip.obj Y)]
  [∀ Y, PreservesFiniteColimits (F.flip.obj Y)]
  [∀ X, (F.obj X).Linear R] [∀ Y, (F.flip.obj Y).Linear R]

local instance (Y : D) : (F.flip.obj Y).Additive := { }

example {X₀ X₁ : C} {Y₀ Y₁ : D}
    {p q n : ℕ} (h : p + q = n) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) :
    F.extBifunctorLinearMap (R := R) X₀ X₁ Y₀ Y₁ p q n h x y = F.extBifunctor x y h :=
  F.extBifunctorLinearMap_apply_apply (R := R) h x y

example
    {X₀ X₁ : C} {Y₀ Y₁ : D} {U V : E}
    (s : U ⟶ (F.obj X₀).obj Y₀) (t : (F.obj X₁).obj Y₁ ⟶ V)
    {p q n : ℕ} (h : p + q = n) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) :
    F.extBifunctorLinearMapWithMaps (R := R) s t h x y =
      ((Ext.mk₀ s).comp (F.extBifunctor x y h) (Nat.zero_add n)).comp
        (Ext.mk₀ t) (Nat.add_zero n) :=
  F.extBifunctorLinearMapWithMaps_apply_apply (R := R) s t h x y

example {X₀ X₁ : C} {Y₀ Y₁ : D}
    {p q n : ℕ} (h : p + q = n) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) :
    F.extBifunctorTensorMap (R := R) X₀ X₁ Y₀ Y₁ p q n h (x ⊗ₜ[R] y) =
      F.extBifunctor x y h :=
  F.extBifunctorTensorMap_tmul (R := R) h x y

end Linear

section Effacement

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]

-- No injective or projective supply is needed by the native ingredient.
example {X Y : C} (n : ℕ) (x : Ext.{w₁} X Y (n + 1)) :
    ∃ (Z : C) (p : Z ⟶ X), Epi p ∧ (Ext.mk₀ p).comp x (zero_add (n + 1)) = 0 :=
  CategoryTheory.Abelian.exists_epi_mk₀_comp_eq_zero n x

end Effacement
