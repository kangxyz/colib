/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Stages
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Tensor products at finite stabilization stages

The tensor product of realizations at levels `n` and `m` realizes the product
at level `n + m`. Increasing the right stage appends one twist. Increasing
the left stage moves the new twist to the right using the braiding. These
two calculations agree when the twist object has trivial self-braiding.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open scoped MonoidalCategory

universe v u
namespace CategoryTheory.Stabilization

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
variable (L : C)

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The result of appending the twist object a specified number of times. -/
abbrev iterateTensorObj (p : ℕ) (A : C) : C := (iterate (tensorRight L) p).obj A

/-- Move an appended twist from the left factor to the end of a product. -/
def moveTensorLeft (A B : C) : (A ⊗ L) ⊗ B ≅ (A ⊗ B) ⊗ L :=
  α_ A L B ≪≫ whiskerLeftIso A (β_ L B) ≪≫ (α_ A B L).symm

/-- Move an appended twist from the right factor to the end of a product. -/
def moveTensorRight (A B : C) : A ⊗ (B ⊗ L) ≅ (A ⊗ B) ⊗ L :=
  (α_ A B L).symm

@[reassoc]
private lemma moveTensorLeft_natural {A B A' B' : C} (f : A ⟶ A') (g : B ⟶ B') :
    ((f ▷ L) ⊗ₘ g) ≫ (moveTensorLeft L A' B').hom =
      (moveTensorLeft L A B).hom ≫ ((f ⊗ₘ g) ▷ L) := by
  simp only [moveTensorLeft, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, Category.assoc,
    ← tensorHom_id, ← id_tensorHom]
  rw [associator_naturality_assoc, tensorHom_comp_tensorHom_assoc, Category.comp_id,
    braiding_naturality, ← Category.id_comp f, ← tensorHom_comp_tensorHom_assoc,
    associator_inv_naturality, Category.id_comp]

omit [BraidedCategory C] in
@[reassoc]
private lemma moveTensorRight_natural {A B A' B' : C} (f : A ⟶ A') (g : B ⟶ B') :
    (f ⊗ₘ (g ▷ L)) ≫ (moveTensorRight L A' B').hom =
      (moveTensorRight L A B).hom ≫ ((f ⊗ₘ g) ▷ L) := by
  simpa only [moveTensorRight, Iso.symm_hom, tensorHom_id] using
    associator_inv_naturality f g (𝟙 L)

@[reassoc]
private lemma moveTensorLeft_moveTensorRight (hL : (β_ L L).hom = 𝟙 _) (A B : C) :
    (moveTensorRight L (A ⊗ L) B).hom ≫ (moveTensorLeft L A B).hom ▷ L =
      (moveTensorLeft L A (B ⊗ L)).hom ≫ (moveTensorRight L A B).hom ▷ L := by
  simp only [moveTensorRight, moveTensorLeft, Iso.symm_hom, Iso.trans_hom, whiskerLeftIso_hom,
    braiding_tensor_right_hom, hL, whiskerLeft_id]
  monoidal

/-- Collect the twists of the left factor to the right of the tensor product. -/
def iterateTensorLeftIso (A B : C) : ∀ p : ℕ,
    iterateTensorObj L p A ⊗ B ≅ iterateTensorObj L p (A ⊗ B)
  | 0 => Iso.refl _
  | p + 1 => moveTensorLeft L (iterateTensorObj L p A) B ≪≫
      whiskerRightIso (iterateTensorLeftIso A B p) L

/-- Collect the twists of both factors at the end of their product. -/
def iterateTensorIso (A B : C) (p : ℕ) : ∀ q : ℕ,
    iterateTensorObj L p A ⊗ iterateTensorObj L q B ≅ iterateTensorObj L (p + q) (A ⊗ B)
  | 0 => iterateTensorLeftIso L A B p
  | q + 1 => moveTensorRight L (iterateTensorObj L p A) (iterateTensorObj L q B) ≪≫
      whiskerRightIso (iterateTensorIso A B p q) L

/-- Collecting twists after adding one on the left agrees with moving the new twist last. -/
lemma iterateTensorIso_left_succ (hL : (β_ L L).hom = 𝟙 _) (A B : C) (p q : ℕ) :
    iterateTensorIso L A B (p + 1) q =
      moveTensorLeft L (iterateTensorObj L p A) (iterateTensorObj L q B) ≪≫
        whiskerRightIso (iterateTensorIso L A B p q) L ≪≫
        eqToIso (congrArg (fun k => iterateTensorObj L k (A ⊗ B)) (Nat.succ_add p q).symm) := by
  induction q with
  | zero =>
      change moveTensorLeft L (iterateTensorObj L p A) B ≪≫
        whiskerRightIso (iterateTensorLeftIso L A B p) L = _
      have he : eqToIso (congrArg (fun k => iterateTensorObj L k (A ⊗ B)) (Nat.succ_add p 0).symm) =
          Iso.refl (iterateTensorObj L (p + 1) (A ⊗ B)) := eqToIso_refl _
      rw [he]
      apply Iso.ext
      simp only [iterateTensorIso, Iso.trans_hom, Iso.refl_hom]
      change _ = (moveTensorLeft L (iterateTensorObj L p A) B).hom ≫
        (whiskerRightIso (iterateTensorLeftIso L A B p) L).hom ≫
        𝟙 (iterateTensorObj L p (A ⊗ B) ⊗ L)
      rw [Category.comp_id]
  | succ q ih =>
      apply Iso.ext
      simp only [iterateTensorIso, ih, Iso.trans_hom, whiskerRightIso_hom,
        comp_whiskerRight, Category.assoc, eqToIso.hom, eqToHom_whiskerRight]
      change (moveTensorRight L (iterateTensorObj L p A ⊗ L) (iterateTensorObj L q B)).hom ≫
          (moveTensorLeft L (iterateTensorObj L p A) (iterateTensorObj L q B)).hom ▷ L ≫ _ = _
      rw [moveTensorLeft_moveTensorRight_assoc L hL]
      rfl


private lemma iterateTensorIso_reindex (A B : C) {p p' q q' : ℕ}
    (hp : p = p') (hq : q = q') :
    (eqToIso (congrArg (fun k => iterateTensorObj L k A) hp) ⊗ᵢ
      eqToIso (congrArg (fun k => iterateTensorObj L k B) hq)) ≪≫ iterateTensorIso L A B p' q' =
      iterateTensorIso L A B p q ≪≫
        eqToIso (congrArg (fun k => iterateTensorObj L k (A ⊗ B)) (congrArg₂ (· + ·) hp hq)) := by
  subst p' q'
  apply Iso.ext
  simp

/-- Numerators tensor and denominators add. -/
def tensorObj (X Y : Stabilization (tensorRight L)) : Stabilization (tensorRight L) :=
  ⟨X.obj ⊗ Y.obj, X.level + Y.level⟩

omit [BraidedCategory C] in
private lemma tensorObj_level (X Y : Stabilization (tensorRight L)) :
    (tensorObj L X Y).level = X.level + Y.level := rfl

/-- A tensor product of two realizations realizes the stable tensor product at their sum. -/
def stageTensorIso (X Y : Stabilization (tensorRight L)) {n m : ℕ}
    (hX : X.level ≤ n) (hY : Y.level ≤ m) :
    stage (tensorRight L) X n ⊗ stage (tensorRight L) Y m ≅
      stage (tensorRight L) (tensorObj L X Y) (n + m) :=
  iterateTensorIso L X.obj Y.obj (n - X.level) (m - Y.level) ≪≫
    eqToIso (congrArg (fun k => iterateTensorObj L k (X.obj ⊗ Y.obj)) (by
      rw [tensorObj_level]
      omega))

/-- At a successor stage the previous realization is tensored with one more copy of `L`. -/
def tensorStageStepIso (X : Stabilization (tensorRight L)) {n n' : ℕ}
    (hX : X.level ≤ n) (hn : n' = n + 1) :
    stage (tensorRight L) X n ⊗ L ≅ stage (tensorRight L) X n' :=
  eqToIso (congrArg (fun k => iterateTensorObj L k X.obj)
    (by omega : n - X.level + 1 = n' - X.level))

omit [BraidedCategory C] in
/-- The successor transition tensors the map with the identity of the twist object. -/
lemma transition_tensorStageStepIso {X Y : Stabilization (tensorRight L)} {n n' : ℕ}
    (hX : X.level ≤ n) (hY : Y.level ≤ n) (hn : n' = n + 1)
    (f : stage (tensorRight L) X n ⟶ stage (tensorRight L) Y n) :
    transition (tensorRight L) hX hY (show n ≤ n' by omega) f =
      (tensorStageStepIso L X hX hn).inv ≫ (f ▷ L) ≫ (tensorStageStepIso L Y hY hn).hom := by
  have hfun : iterate (tensorRight L) (n' - n) = iterate (tensorRight L) 1 :=
    congrArg _ (by omega)
  rw [transition, Functor.congr_hom hfun f]
  simp only [stageIso, tensorStageStepIso, eqToIso.hom, eqToIso.inv, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]
  rfl

private lemma stageTensorIso_left_step (hL : (β_ L L).hom = 𝟙 _)
    (X Y : Stabilization (tensorRight L)) {n n' m : ℕ}
    (hX : X.level ≤ n) (hY : Y.level ≤ m) (hn : n' = n + 1) :
    (tensorStageStepIso L X hX hn ⊗ᵢ Iso.refl (stage (tensorRight L) Y m)) ≪≫
        stageTensorIso L X Y (show X.level ≤ n' by omega) hY =
      moveTensorLeft L (stage (tensorRight L) X n) (stage (tensorRight L) Y m) ≪≫
        whiskerRightIso (stageTensorIso L X Y hX hY) L ≪≫
        tensorStageStepIso L (tensorObj L X Y) (Nat.add_le_add hX hY)
          (show n' + m = (n + m) + 1 by omega) := by
  let p := n - X.level
  let q := m - Y.level
  have hp : p + 1 = n' - X.level := by dsimp [p]; omega
  have e := iterateTensorIso_reindex L X.obj Y.obj hp (rfl : q = q)
  apply Iso.ext
  have eh := congrArg Iso.hom e
  simp only [Iso.trans_hom, tensorIso_hom, eqToIso.hom, eqToIso_refl, Iso.refl_hom,
    tensorHom_id] at eh
  simp only [stageTensorIso, tensorStageStepIso, Iso.trans_hom, tensorIso_hom,
    eqToIso.hom, Iso.refl_hom, tensorHom_id, whiskerRightIso_hom,
    comp_whiskerRight, Category.assoc]
  change
    (eqToHom (congrArg (fun k => iterateTensorObj L k X.obj) hp) ▷ iterateTensorObj L q Y.obj) ≫
      (iterateTensorIso L X.obj Y.obj (n' - X.level) q).hom ≫ _ = _
  rw [reassoc_of% eh, iterateTensorIso_left_succ L hL]
  simp only [Iso.trans_hom, whiskerRightIso_hom, eqToIso.hom, Category.assoc,
    eqToHom_trans, eqToHom_whiskerRight]
  rfl

private lemma stageTensorIso_right_step
    (X Y : Stabilization (tensorRight L)) {n m m' : ℕ}
    (hX : X.level ≤ n) (hY : Y.level ≤ m) (hm : m' = m + 1) :
    (Iso.refl (stage (tensorRight L) X n) ⊗ᵢ tensorStageStepIso L Y hY hm) ≪≫
        stageTensorIso L X Y hX (show Y.level ≤ m' by omega) =
      moveTensorRight L (stage (tensorRight L) X n) (stage (tensorRight L) Y m) ≪≫
        whiskerRightIso (stageTensorIso L X Y hX hY) L ≪≫
        tensorStageStepIso L (tensorObj L X Y) (Nat.add_le_add hX hY)
          (show n + m' = (n + m) + 1 by omega) := by
  let p := n - X.level
  let q := m - Y.level
  have hq : q + 1 = m' - Y.level := by dsimp [q]; omega
  have e := iterateTensorIso_reindex L X.obj Y.obj (rfl : p = p) hq
  apply Iso.ext
  have eh := congrArg Iso.hom e
  simp only [Iso.trans_hom, tensorIso_hom, eqToIso.hom, eqToIso_refl, Iso.refl_hom,
    id_tensorHom] at eh
  simp only [stageTensorIso, tensorStageStepIso, Iso.trans_hom, tensorIso_hom,
    eqToIso.hom, Iso.refl_hom, id_tensorHom, whiskerRightIso_hom,
    comp_whiskerRight, Category.assoc]
  change
    (iterateTensorObj L p X.obj ◁ eqToHom (congrArg (fun k => iterateTensorObj L k Y.obj) hq)) ≫
      (iterateTensorIso L X.obj Y.obj p (m' - Y.level)).hom ≫ _ = _
  rw [reassoc_of% eh]
  simp only [iterateTensorIso, Iso.trans_hom, whiskerRightIso_hom, Category.assoc,
    eqToHom_trans, eqToHom_whiskerRight]
  rfl


omit [BraidedCategory C] in
private lemma tensorHom_conjugate {A B C₀ D A' B' C' D' : C}
    (eA : A ≅ A') (eB : B ≅ B') (eC : C₀ ≅ C') (eD : D ≅ D')
    (f : A ⟶ B) (g : C₀ ⟶ D) :
    (eA.inv ≫ f ≫ eB.hom) ⊗ₘ (eC.inv ≫ g ≫ eD.hom) =
      (eA ⊗ᵢ eC).inv ≫ (f ⊗ₘ g) ≫ (eB ⊗ᵢ eD).hom := by
  rw [tensorIso_inv, tensorIso_hom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]

omit [MonoidalCategory C] [BraidedCategory C] in
private lemma conjugate_trans {A B A' B' A'' B'' : C}
    (eA : A ≅ A') (eB : B ≅ B') (eA' : A' ≅ A'') (eB' : B' ≅ B'')
    (f : A ⟶ B) :
    eA'.inv ≫ (eA.inv ≫ f ≫ eB.hom) ≫ eB'.hom =
      (eA ≪≫ eA').inv ≫ f ≫ (eB ≪≫ eB').hom := by
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]

/-- Tensor maps represented at two chosen finite stages. -/
def tensorStageHom {X X' Y Y' : Stabilization (tensorRight L)} {n m : ℕ}
    (hX : X.level ≤ n) (hX' : X'.level ≤ n) (hY : Y.level ≤ m) (hY' : Y'.level ≤ m)
    (f : stage (tensorRight L) X n ⟶ stage (tensorRight L) X' n)
    (g : stage (tensorRight L) Y m ⟶ stage (tensorRight L) Y' m) :
    stage (tensorRight L) (tensorObj L X Y) (n + m) ⟶
      stage (tensorRight L) (tensorObj L X' Y') (n + m) :=
  (stageTensorIso L X Y hX hY).inv ≫ (f ⊗ₘ g) ≫ (stageTensorIso L X' Y' hX' hY').hom

private lemma tensorStageHom_left_step (hL : (β_ L L).hom = 𝟙 _)
    {X X' Y Y' : Stabilization (tensorRight L)} {n n' m : ℕ}
    (hX : X.level ≤ n) (hX' : X'.level ≤ n) (hY : Y.level ≤ m) (hY' : Y'.level ≤ m)
    (hn : n' = n + 1)
    (f : stage (tensorRight L) X n ⟶ stage (tensorRight L) X' n)
    (g : stage (tensorRight L) Y m ⟶ stage (tensorRight L) Y' m) :
    transition (tensorRight L) (Nat.add_le_add hX hY) (Nat.add_le_add hX' hY')
      (Nat.add_le_add_right (show n ≤ n' by omega) m) (tensorStageHom L hX hX' hY hY' f g) =
    tensorStageHom L (show X.level ≤ n' by omega) (show X'.level ≤ n' by omega) hY hY'
      (transition (tensorRight L) hX hX' (show n ≤ n' by omega) f) g := by
  let e := tensorStageStepIso L X hX hn
  let e' := tensorStageStepIso L X' hX' hn
  let d := tensorStageStepIso L (tensorObj L X Y) (Nat.add_le_add hX hY)
    (show n' + m = (n + m) + 1 by omega)
  let d' := tensorStageStepIso L (tensorObj L X' Y') (Nat.add_le_add hX' hY')
    (show n' + m = (n + m) + 1 by omega)
  let a := stageTensorIso L X Y hX hY
  let a' := stageTensorIso L X' Y' hX' hY'
  let b := stageTensorIso L X Y (show X.level ≤ n' by omega) hY
  let b' := stageTensorIso L X' Y' (show X'.level ≤ n' by omega) hY'
  rw [transition_tensorStageStepIso L _ _ (show n' + m = (n + m) + 1 by omega),
    transition_tensorStageStepIso L hX hX' hn]
  change d.inv ≫ (a.inv ≫ (f ⊗ₘ g) ≫ a'.hom) ▷ L ≫ d'.hom =
    b.inv ≫ ((e.inv ≫ (f ▷ L) ≫ e'.hom) ⊗ₘ g) ≫ b'.hom
  rw [show g = (Iso.refl _).inv ≫ g ≫ (Iso.refl _).hom by simp,
    tensorHom_conjugate, conjugate_trans,
    stageTensorIso_left_step L hL, stageTensorIso_left_step L hL]
  simp only [Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id, Iso.trans_hom,
    Iso.trans_inv, whiskerRightIso_hom, whiskerRightIso_inv, comp_whiskerRight, Category.assoc]
  rw [moveTensorLeft_natural_assoc L, Iso.inv_hom_id_assoc]

private lemma tensorStageHom_right_step
    {X X' Y Y' : Stabilization (tensorRight L)} {n m m' : ℕ}
    (hX : X.level ≤ n) (hX' : X'.level ≤ n) (hY : Y.level ≤ m) (hY' : Y'.level ≤ m)
    (hm : m' = m + 1)
    (f : stage (tensorRight L) X n ⟶ stage (tensorRight L) X' n)
    (g : stage (tensorRight L) Y m ⟶ stage (tensorRight L) Y' m) :
    transition (tensorRight L) (Nat.add_le_add hX hY) (Nat.add_le_add hX' hY')
      (Nat.add_le_add_left (show m ≤ m' by omega) n) (tensorStageHom L hX hX' hY hY' f g) =
    tensorStageHom L hX hX' (show Y.level ≤ m' by omega) (show Y'.level ≤ m' by omega)
      f (transition (tensorRight L) hY hY' (show m ≤ m' by omega) g) := by
  let e := tensorStageStepIso L Y hY hm
  let e' := tensorStageStepIso L Y' hY' hm
  let d := tensorStageStepIso L (tensorObj L X Y) (Nat.add_le_add hX hY)
    (show n + m' = (n + m) + 1 by omega)
  let d' := tensorStageStepIso L (tensorObj L X' Y') (Nat.add_le_add hX' hY')
    (show n + m' = (n + m) + 1 by omega)
  let a := stageTensorIso L X Y hX hY
  let a' := stageTensorIso L X' Y' hX' hY'
  let b := stageTensorIso L X Y hX (show Y.level ≤ m' by omega)
  let b' := stageTensorIso L X' Y' hX' (show Y'.level ≤ m' by omega)
  rw [transition_tensorStageStepIso L _ _ (show n + m' = (n + m) + 1 by omega),
    transition_tensorStageStepIso L hY hY' hm]
  change d.inv ≫ (a.inv ≫ (f ⊗ₘ g) ≫ a'.hom) ▷ L ≫ d'.hom =
    b.inv ≫ (f ⊗ₘ (e.inv ≫ (g ▷ L) ≫ e'.hom)) ≫ b'.hom
  rw [show f = (Iso.refl _).inv ≫ f ≫ (Iso.refl _).hom by simp,
    tensorHom_conjugate, conjugate_trans,
    stageTensorIso_right_step L, stageTensorIso_right_step L]
  simp only [Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id, Iso.trans_hom,
    Iso.trans_inv, whiskerRightIso_hom, whiskerRightIso_inv, comp_whiskerRight, Category.assoc]
  rw [moveTensorRight_natural_assoc L, Iso.inv_hom_id_assoc]


private lemma tensorStageHom_left_le (hL : (β_ L L).hom = 𝟙 _)
    {X X' Y Y' : Stabilization (tensorRight L)} {n n' m : ℕ}
    (hX : X.level ≤ n) (hX' : X'.level ≤ n) (hY : Y.level ≤ m) (hY' : Y'.level ≤ m)
    (hn : n ≤ n')
    (f : stage (tensorRight L) X n ⟶ stage (tensorRight L) X' n)
    (g : stage (tensorRight L) Y m ⟶ stage (tensorRight L) Y' m) :
    transition (tensorRight L) (Nat.add_le_add hX hY) (Nat.add_le_add hX' hY')
      (Nat.add_le_add_right hn m) (tensorStageHom L hX hX' hY hY' f g) =
    tensorStageHom L (hX.trans hn) (hX'.trans hn) hY hY'
      (transition (tensorRight L) hX hX' hn f) g := by
  induction hn with
  | refl => simp
  | @step k hk ih =>
      rw [← transition_trans (tensorRight L) (Nat.add_le_add hX hY)
          (Nat.add_le_add hX' hY') (Nat.add_le_add_right hk m)
          (Nat.add_le_add_right (Nat.le_succ k) m),
        ih, tensorStageHom_left_step L hL _ _ _ _ (rfl : k + 1 = k + 1),
        transition_trans]

private lemma tensorStageHom_right_le
    {X X' Y Y' : Stabilization (tensorRight L)} {n m m' : ℕ}
    (hX : X.level ≤ n) (hX' : X'.level ≤ n) (hY : Y.level ≤ m) (hY' : Y'.level ≤ m)
    (hm : m ≤ m')
    (f : stage (tensorRight L) X n ⟶ stage (tensorRight L) X' n)
    (g : stage (tensorRight L) Y m ⟶ stage (tensorRight L) Y' m) :
    transition (tensorRight L) (Nat.add_le_add hX hY) (Nat.add_le_add hX' hY')
      (Nat.add_le_add_left hm n) (tensorStageHom L hX hX' hY hY' f g) =
    tensorStageHom L hX hX' (hY.trans hm) (hY'.trans hm)
      f (transition (tensorRight L) hY hY' hm g) := by
  induction hm with
  | refl => simp
  | @step k hk ih =>
      rw [← transition_trans (tensorRight L) (Nat.add_le_add hX hY)
          (Nat.add_le_add hX' hY') (Nat.add_le_add_left hk n)
          (Nat.add_le_add_left (Nat.le_succ k) n),
        ih, tensorStageHom_right_step L _ _ _ _ (rfl : k + 1 = k + 1),
        transition_trans]

/-- Increasing the input stages before tensoring agrees with increasing the output stage. -/
lemma tensorStageHom_transition (hL : (β_ L L).hom = 𝟙 _)
    {X X' Y Y' : Stabilization (tensorRight L)} {n n' m m' : ℕ}
    (hX : X.level ≤ n) (hX' : X'.level ≤ n) (hY : Y.level ≤ m) (hY' : Y'.level ≤ m)
    (hn : n ≤ n') (hm : m ≤ m')
    (f : stage (tensorRight L) X n ⟶ stage (tensorRight L) X' n)
    (g : stage (tensorRight L) Y m ⟶ stage (tensorRight L) Y' m) :
    transition (tensorRight L) (Nat.add_le_add hX hY) (Nat.add_le_add hX' hY')
      (Nat.add_le_add hn hm) (tensorStageHom L hX hX' hY hY' f g) =
    tensorStageHom L (hX.trans hn) (hX'.trans hn) (hY.trans hm) (hY'.trans hm)
      (transition (tensorRight L) hX hX' hn f) (transition (tensorRight L) hY hY' hm g) := by
  rw [← transition_trans (tensorRight L) (Nat.add_le_add hX hY)
      (Nat.add_le_add hX' hY') (Nat.add_le_add_right hn m) (Nat.add_le_add_left hm n'),
    tensorStageHom_left_le L hL, tensorStageHom_right_le L]

end CategoryTheory.Stabilization
