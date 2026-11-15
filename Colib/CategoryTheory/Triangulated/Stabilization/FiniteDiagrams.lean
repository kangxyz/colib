/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.EquivFin

/-! # Lifting finite diagrams to a common twist

A diagram whose objects have bounded denominators lifts, including all its
commutativity relations, to the original category at any common stage.
-/

@[expose] public noncomputable section

universe v u v' u'

namespace CategoryTheory.Stabilization

variable {C : Type u} [Category.{v} C] (T : C ⥤ C) [T.Full] [T.Faithful]

/-- An isomorphism of stable objects is specified by an isomorphism at a common stage. -/
def isoOfStage (X Y : Stabilization T) (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n)
    (e : stage T X n ≅ stage T Y n) : X ≅ Y where
  hom := (homEquiv T X Y n hX hY).symm e.hom
  inv := (homEquiv T Y X n hY hX).symm e.inv
  hom_inv_id := by
    apply hom_ext T n hX hX
    rw [homEquiv_comp T _ _ n hX hY hX]
    simp
  inv_hom_id := by
    apply hom_ext T n hY hY
    rw [homEquiv_comp T _ _ n hY hX hY]
    simp

/-- Realizing an object included at level `n` at that same level recovers it. -/
def atLevelStageIso (n : ℕ) (A : C) : stage T ((atLevel T n).obj A) n ≅ A :=
  eqToIso (by simp [atLevel, stage])

/-- Realizing an included arrow at a larger stage applies the corresponding iterate of `T`. -/
lemma homEquiv_atLevel_map_of_le (a n : ℕ) (h : a ≤ n) {A B : C} (f : A ⟶ B) :
    homEquiv T ((atLevel T a).obj A) ((atLevel T a).obj B) n h h
      ((atLevel T a).map f) = (iterate T (n - a)).map f := by
  let X : Stabilization T := ⟨A, a⟩
  let Y : Stabilization T := ⟨B, a⟩
  let eA : A = stage T X (max a a) := by simp [X, stage]
  let eB : B = stage T Y (max a a) := by simp [Y, stage]
  change transition T (X := X) (Y := Y) (Nat.le_max_left a a) (Nat.le_max_right a a)
    (max_le h h) (eqToHom eA.symm ≫ f ≫ eqToHom eB) = _
  dsimp only [transition, stageIso, eqToIso]
  have hfun : iterate T (n - a) = iterate T (n - max a a) := by rw [max_self]
  rw [Functor.congr_hom hfun f]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans]
  rfl

/-- The original map is recovered when its inclusion is realized at its own level. -/
lemma homEquiv_atLevel_map (n : ℕ) {A B : C} (f : A ⟶ B) :
    homEquiv T ((atLevel T n).obj A) ((atLevel T n).obj B) n
      (Nat.le_refl _) (Nat.le_refl _) ((atLevel T n).map f) =
      (atLevelStageIso T n A).hom ≫ f ≫ (atLevelStageIso T n B).inv := by
  rw [homEquiv_atLevel_map_of_le T n n (Nat.le_refl n)]
  have hfun : iterate T (n - n) = 𝟭 C := by rw [Nat.sub_self, iterate_zero]
  exact Functor.congr_hom hfun f

/-- Clearing the denominator of an object gives a canonical isomorphism. -/
def rebaseIso (X : Stabilization T) (n : ℕ) (hX : X.level ≤ n) :
    X ≅ (atLevel T n).obj (stage T X n) :=
  isoOfStage T X _ n hX (Nat.le_refl _) (atLevelStageIso T n _).symm

section Diagrams

variable {J : Type u'} [Category.{v'} J] (F : J ⥤ Stabilization T)
  (n : ℕ) (h : ∀ j, (F.obj j).level ≤ n)

/-- Lift a diagram with bounded denominators, preserving its actual arrows and equations. -/
def liftDiagram : J ⥤ C where
  obj j := stage T (F.obj j) n
  map {j k} f := homEquiv T _ _ n (h j) (h k) (F.map f)
  map_id j := by rw [F.map_id, homEquiv_id]
  map_comp {i j k} f g := by rw [F.map_comp, homEquiv_comp T _ _ n (h i) (h j) (h k)]

/-- The lifted diagram represents the original diagram at the chosen common level. -/
def liftDiagramIso : F ≅ liftDiagram T F n h ⋙ atLevel T n :=
  NatIso.ofComponents (fun j => rebaseIso T (F.obj j) n (h j)) (by
    intro j k f
    let fₙ : stage T (F.obj j) n ⟶ stage T (F.obj k) n :=
      homEquiv T _ _ n (h j) (h k) (F.map f)
    change F.map f ≫ (rebaseIso T (F.obj k) n (h k)).hom =
      (rebaseIso T (F.obj j) n (h j)).hom ≫ (atLevel T n).map fₙ
    have hb (i : J) : ((atLevel T n).obj (stage T (F.obj i) n)).level ≤ n := Nat.le_refl n
    apply hom_ext T n (h j) (hb k)
    rw [homEquiv_comp T _ _ n (h j) (h k) (hb k),
      homEquiv_comp T _ _ n (h j) (hb j) (hb k),
      homEquiv_atLevel_map T n fₙ]
    simp [rebaseIso, isoOfStage, fₙ])

end Diagrams

/-- Every finite diagram has a common finite stage, including its commutativity relations. -/
theorem finite_diagram_lifts {J : Type u'} [Category.{v'} J] [Finite J]
    (F : J ⥤ Stabilization T) :
    ∃ (n : ℕ) (G : J ⥤ C), Nonempty (F ≅ G ⋙ atLevel T n) := by
  classical
  let := Fintype.ofFinite J
  let n := Finset.univ.sup (fun j => (F.obj j).level)
  have h (j : J) : (F.obj j).level ≤ n :=
    Finset.le_sup (f := fun i : J => (F.obj i).level) (Finset.mem_univ j)
  exact ⟨n, liftDiagram T F n h, ⟨liftDiagramIso T F n h⟩⟩

end CategoryTheory.Stabilization
