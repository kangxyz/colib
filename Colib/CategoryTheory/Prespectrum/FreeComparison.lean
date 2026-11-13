/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Prespectrum.Free
import all Colib.CategoryTheory.Prespectrum.Free

/-!
# Transport of a free prespectrum

A functor preserving the initial object and commuting with suspension
carries the free prespectrum in a given degree to the free prespectrum
on the image of its generator.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace CategoryTheory.SequentialPrespectrum

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {S : C ⥤ C} {T : D ⥤ D} (F : C ⥤ D) (α : F ⋙ T ≅ S ⋙ F)

private def isoOfLevels {X Y : SequentialPrespectrum T} (e : ∀ n, X.level n ≅ Y.level n)
    (h : ∀ n, X.bonding n ≫ (e (n + 1)).hom = T.map (e n).hom ≫ Y.bonding n) : X ≅ Y where
  hom := ⟨fun n => (e n).hom, h⟩
  inv := ⟨fun n => (e n).inv, fun n => by
    apply (cancel_mono (e (n + 1)).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, h,
      ← Category.assoc, ← T.map_comp, Iso.inv_hom_id, T.map_id, Category.id_comp]⟩
  hom_inv_id := Hom.ext (funext fun n => (e n).hom_inv_id)
  inv_hom_id := Hom.ext (funext fun n => (e n).inv_hom_id)

set_option backward.isDefEq.respectTransparency false in
private def suspensionMapLevelIso (X : C) :
    (n : ℕ) → ((mapFunctor F α).obj ((suspension S).obj X)).level n ≅
      ((suspension T).obj (F.obj X)).level n
  | 0 => Iso.refl _
  | n + 1 =>
    (α.app ((suspension S).obj X |>.level n)).symm ≪≫ T.mapIso (suspensionMapLevelIso X n)

set_option backward.isDefEq.respectTransparency false in
private def suspensionMapIso (X : C) :
    (mapFunctor F α).obj ((suspension S).obj X) ≅ (suspension T).obj (F.obj X) :=
  isoOfLevels (suspensionMapLevelIso F α X) (fun n => by
    let e := suspensionMapLevelIso F α X n
    let a := α.app (((suspension S).obj X).level n)
    let g : T.obj (((mapFunctor F α).obj ((suspension S).obj X)).level n) ⟶
        T.obj (((suspension T).obj (F.obj X)).level n) := T.map e.hom
    have h : F.map (𝟙 (S.obj (((suspension S).obj X).level n))) = 𝟙 _ := F.map_id _
    change (a.hom ≫ F.map (𝟙 _)) ≫ a.inv ≫ g = g ≫ 𝟙 _
    calc
      _ = (a.hom ≫ 𝟙 ((S ⋙ F).obj (((suspension S).obj X).level n))) ≫ a.inv ≫ g :=
        congrArg (fun t => (a.hom ≫ t) ≫ a.inv ≫ g) h
      _ = a.hom ≫ a.inv ≫ g := congrArg (fun t => t ≫ a.inv ≫ g) (Category.comp_id a.hom)
      _ = g := a.hom_inv_id_assoc g
      _ = _ := (Category.comp_id g).symm)

variable [HasInitial C] [HasInitial D]
  [PreservesColimit (Functor.empty.{0} C) S] [PreservesColimit (Functor.empty.{0} D) T]
  [PreservesColimit (Functor.empty.{0} C) F]

set_option backward.isDefEq.respectTransparency false in
private def prependInitialMapIso (X : SequentialPrespectrum S) (Y : SequentialPrespectrum T)
    (e : (mapFunctor F α).obj X ≅ Y) :
    (mapFunctor F α).obj ((prependInitial S).obj X) ≅ (prependInitial T).obj Y := by
  let h₀ := (initialIsInitial (C := C)).isInitialObj F (⊥_ C)
  let a : ∀ n, ((mapFunctor F α).obj ((prependInitial S).obj X)).level n ≅
      ((prependInitial T).obj Y).level n
    | 0 => h₀.uniqueUpToIso initialIsInitial
    | n + 1 => (evaluation n).mapIso e
  refine isoOfLevels a ?_
  intro n
  cases n with
  | zero =>
    apply ((isColimitOfHasInitialOfPreservesColimit T).ofIso
      (T.mapIso (h₀.uniqueUpToIso initialIsInitial)).symm).hom_ext
  | succ n => exact e.hom.comm n

set_option backward.isDefEq.respectTransparency false in
/-- Transporting the free prespectrum preserves the original free generator. -/
@[no_expose]
def freeAtMapIso : ∀ (n : ℕ) (X : C),
    (mapFunctor F α).obj ((freeAt (S := S) n).obj X) ≅ (freeAt (S := T) n).obj (F.obj X)
  | 0, X => suspensionMapIso F α X
  | n + 1, X => prependInitialMapIso F α _ _ (freeAtMapIso n X)

omit [HasInitial C] [HasInitial D]
  [PreservesColimit (Functor.empty.{0} C) S] [PreservesColimit (Functor.empty.{0} D) T]
  [PreservesColimit (Functor.empty.{0} C) F] in
set_option backward.isDefEq.respectTransparency false in
private theorem suspensionMapIso_hom_naturality {X Y : C} (f : X ⟶ Y) :
    (mapFunctor F α).map ((suspension S).map f) ≫ (suspensionMapIso F α Y).hom =
      (suspensionMapIso F α X).hom ≫ (suspension T).map (F.map f) := by
  apply Hom.ext
  funext n
  induction n with
  | zero =>
    change F.map f ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
    rw [Category.comp_id, Category.id_comp]
  | succ n ih =>
    let e := suspensionMapLevelIso F α X n
    let e' := suspensionMapLevelIso F α Y n
    let g := (suspension S).map f |>.app n
    let t := (suspension T).map (F.map f) |>.app n
    let a := α.app (((suspension S).obj X).level n)
    let a' := α.app (((suspension S).obj Y).level n)
    have h : F.map g ≫ e'.hom = e.hom ≫ t := ih
    have ha : F.map (S.map g) ≫ a'.inv = a.inv ≫ T.map (F.map g) := α.inv.naturality g
    change F.map (S.map g) ≫ a'.inv ≫ T.map e'.hom =
      (a.inv ≫ T.map e.hom) ≫ T.map t
    calc
      _ = a.inv ≫ T.map (F.map g) ≫ T.map e'.hom := (reassoc_of% ha) _
      _ = a.inv ≫ T.map (F.map g ≫ e'.hom) :=
        (congrArg (a.inv ≫ ·) (T.map_comp _ _)).symm
      _ = a.inv ≫ T.map (e.hom ≫ t) := congrArg (fun g => a.inv ≫ T.map g) h
      _ = _ := (congrArg (a.inv ≫ ·) (T.map_comp _ _)).trans (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem freeAtMapIso_hom_naturality (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (mapFunctor F α).map ((freeAt (S := S) n).map f) ≫ (freeAtMapIso F α n Y).hom =
      (freeAtMapIso F α n X).hom ≫ (freeAt (S := T) n).map (F.map f) := by
  induction n with
  | zero => exact suspensionMapIso_hom_naturality F α f
  | succ n ih =>
    apply Hom.ext
    funext i
    cases i with
    | zero => exact ((initialIsInitial (C := C)).isInitialObj F (⊥_ C)).hom_ext _ _
    | succ i =>
      exact congrArg (fun a :
        (mapFunctor F α).obj ((freeAt (S := S) n).obj X) ⟶
          (freeAt (S := T) n).obj (F.obj Y) => a.app i) ih

/-- Transporting the free prespectrum commutes naturally with changing
the original generator. -/
@[no_expose]
def freeAtMapFunctorIso (n : ℕ) :
    freeAt (S := S) n ⋙ mapFunctor F α ≅ F ⋙ freeAt (S := T) n :=
  NatIso.ofComponents (freeAtMapIso F α n) (fun f => freeAtMapIso_hom_naturality F α n f)

set_option backward.isDefEq.respectTransparency false in
/-- In the generating degree, the transport uses the original generator
identifications on both sides. -/
theorem freeAtMapIso_hom_app_generator (n : ℕ) (X : C) :
    ((freeAtMapIso F α n X).hom.app n) ≫ (freeAtLevelIso (S := T) n (F.obj X)).hom =
      F.map (freeAtLevelIso (S := S) n X).hom := by
  induction n with
  | zero =>
    change (𝟙 (F.obj X)) ≫ eqToHom (freeAt_level (S := T) 0 (F.obj X)) =
      F.map (eqToHom (freeAt_level (S := S) 0 X))
    simp
    rfl
  | succ n ih => exact ih

/-- Maps from the transported free prespectrum are given by the actual
map from the transported generator to the specified level. -/
@[no_expose]
def freeAtMapHomEquiv (n : ℕ) (X : C) (Y : SequentialPrespectrum T) :
    ((mapFunctor F α).obj ((freeAt (S := S) n).obj X) ⟶ Y) ≃ (F.obj X ⟶ Y.level n) :=
  (freeAtMapIso F α n X).homFromEquiv.trans
    ((freeAtAdjunction (S := T) n).homEquiv (F.obj X) Y)

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence evaluates the original component in the generating
degree and uses the transported identification of that level. -/
theorem freeAtMapHomEquiv_apply (n : ℕ) (X : C) (Y : SequentialPrespectrum T)
    (g : (mapFunctor F α).obj ((freeAt (S := S) n).obj X) ⟶ Y) :
    freeAtMapHomEquiv F α n X Y g =
      F.map (freeAtLevelIso (S := S) n X).inv ≫ g.app n := by
  let e := freeAtMapIso F α n X
  let a := F.mapIso (freeAtLevelIso (S := S) n X)
  let b := freeAtLevelIso (S := T) n (F.obj X)
  let c := (evaluation n).mapIso e
  have h : c.hom ≫ b.hom = a.hom := freeAtMapIso_hom_app_generator F α n X
  have hv : b.inv ≫ c.inv = a.inv := by
    apply (cancel_mono a.hom).1
    calc
      (b.inv ≫ c.inv) ≫ a.hom = b.inv ≫ c.inv ≫ c.hom ≫ b.hom :=
        (Category.assoc _ _ _).trans (congrArg (fun f => b.inv ≫ c.inv ≫ f) h.symm)
      _ = 𝟙 (F.obj X) := (congrArg (b.inv ≫ ·) (c.inv_hom_id_assoc b.hom)).trans b.inv_hom_id
      _ = a.inv ≫ a.hom := a.inv_hom_id.symm
  change (freeAtAdjunction (S := T) n).homEquiv (F.obj X) Y (e.inv ≫ g) = _
  rw [freeAtAdjunction_homEquiv_app]
  change b.inv ≫ c.inv ≫ g.app n = a.inv ≫ g.app n
  rw [← Category.assoc, hv]

end CategoryTheory.SequentialPrespectrum
