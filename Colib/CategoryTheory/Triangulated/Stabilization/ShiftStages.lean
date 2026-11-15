/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Stages
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs

/-! # Compatibility of finite stages with cohomological shifts -/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

open CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] (T : C ⥤ C)

/-- The composition comparison for the selected iterates, with explicit coherence. -/
def iterateAddIso (a : ℕ) : (b : ℕ) → iterate T (a + b) ≅ iterate T a ⋙ iterate T b
  | 0 => (iterate T a).rightUnitor.symm
  | b + 1 => isoWhiskerRight (iterateAddIso a b) T ≪≫ Functor.associator _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma iterateAddIso_eqToIso (a b : ℕ) : iterateAddIso T a b = eqToIso (iterate_add T a b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    ext X
    simp [iterateAddIso, ih, eqToIso, eqToHom_map, eqToHom_app]

variable [HasShift C ℤ] [T.CommShift ℤ]

instance iterateCommShift : (n : ℕ) → (iterate T n).CommShift ℤ
  | 0 => inferInstanceAs ((𝟭 C).CommShift ℤ)
  | n + 1 => by
    letI := iterateCommShift n
    exact inferInstanceAs ((iterate T n ⋙ T).CommShift ℤ)

instance iterateAddIso_commShift (a b : ℕ) :
    NatTrans.CommShift (iterateAddIso T a b).hom ℤ := by
  induction b with
  | zero =>
    change NatTrans.CommShift (iterate T a).rightUnitor.inv ℤ
    infer_instance
  | succ b ih =>
    let := ih
    change NatTrans.CommShift
      (whiskerRight (iterateAddIso T a b).hom T ≫ (Functor.associator _ _ _).hom) ℤ
    infer_instance

instance iterateEq_commShift {a b : ℕ} (h : a = b) :
    NatTrans.CommShift (eqToHom (congrArg (iterate T) h)) ℤ := by
  subst b
  change NatTrans.CommShift (𝟙 (iterate T a)) ℤ
  infer_instance

/-- Adding twists from stage `m` to stage `n`, as a natural isomorphism. -/
def stageFunctorIso {a m n : ℕ} (ha : a ≤ m) (h : m ≤ n) :
    iterate T (m - a) ⋙ iterate T (n - m) ≅ iterate T (n - a) :=
  (iterateAddIso T (m - a) (n - m)).symm ≪≫
    eqToIso (congrArg (iterate T) (show (m - a) + (n - m) = n - a by omega))

instance stageFunctorIso_commShift {a m n : ℕ} (ha : a ≤ m) (h : m ≤ n) :
    NatTrans.CommShift (stageFunctorIso T ha h).hom ℤ := by
  have h₁ : NatTrans.CommShift (iterateAddIso T (m - a) (n - m)).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  have he : (m - a) + (n - m) = n - a := by omega
  have h₂ : NatTrans.CommShift (eqToHom (congrArg (iterate T) he)) ℤ :=
    iterateEq_commShift T he
  change NatTrans.CommShift
    ((iterateAddIso T (m - a) (n - m)).inv ≫ eqToHom (congrArg (iterate T) he)) ℤ
  infer_instance

omit [HasShift C ℤ] [T.CommShift ℤ] in
lemma stageFunctorIso_app (X : Stabilization T) {m n : ℕ}
    (hX : X.level ≤ m) (h : m ≤ n) :
    (stageFunctorIso T hX h).app X.obj = stageIso T X hX h := by
  ext
  simp [stageFunctorIso, iterateAddIso_eqToIso, stageIso, eqToHom_app]
  rfl

/-- Cohomological shift changes the numerator and keeps the inverse-twist denominator. -/
abbrev shiftObj (r : ℤ) (X : Stabilization T) : Stabilization T := ⟨X.obj⟦r⟧, X.level⟩

/-- The shifted numerator at a common stage is canonically the shift of that stage. -/
def stageShiftIso (r : ℤ) (X : Stabilization T) (n : ℕ) :
    stage T (shiftObj T r X) n ≅ (stage T X n)⟦r⟧ :=
  ((iterate T (n - X.level)).commShiftIso r).app X.obj

set_option backward.isDefEq.respectTransparency false in
/-- The common-stage comparison respects the chosen shift commutation of `T`. -/
lemma stageIso_shift_hom (r : ℤ) (X : Stabilization T) {m n : ℕ}
    (hX : X.level ≤ m) (h : m ≤ n) :
    (iterate T (n - m)).map (stageShiftIso T r X m).hom ≫
      ((iterate T (n - m)).commShiftIso r).hom.app (stage T X m) ≫
      ((stageIso T X hX h).hom)⟦r⟧' =
      (stageIso T (shiftObj T r X) hX h).hom ≫ (stageShiftIso T r X n).hom := by
  have e := NatTrans.shift_app_comm (stageFunctorIso T hX h).hom r X.obj
  have eX := congrArg Iso.hom (stageFunctorIso_app T X hX h)
  have eXs := congrArg Iso.hom (stageFunctorIso_app T (shiftObj T r X) hX h)
  simp only [Iso.app_hom] at eX eXs
  rw [Functor.commShiftIso_comp_hom_app, eX, eXs] at e
  simpa only [Category.assoc, stageShiftIso, stage, shiftObj, Iso.app_hom] using e

set_option backward.isDefEq.respectTransparency false in
/-- Transporting a shifted morphism to a larger stage is the shift of its transport. -/
lemma transition_shift (r : ℤ) {X Y : Stabilization T} {m n : ℕ}
    (hX : X.level ≤ m) (hY : Y.level ≤ m) (h : m ≤ n)
    (f : stage T X m ⟶ stage T Y m) :
    transition T (X := shiftObj T r X) (Y := shiftObj T r Y) hX hY h
        ((stageShiftIso T r X m).hom ≫ f⟦r⟧' ≫ (stageShiftIso T r Y m).inv) =
      (stageShiftIso T r X n).hom ≫ (transition T hX hY h f)⟦r⟧' ≫
        (stageShiftIso T r Y n).inv := by
  rw [← cancel_epi (stageIso T (shiftObj T r X) hX h).hom,
    ← cancel_mono (stageShiftIso T r Y n).hom]
  simp only [transition, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← stageIso_shift_hom T r Y hY h]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id,
    Functor.map_id, Category.id_comp]
  rw [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality_assoc]
  rw [← reassoc_of% (stageIso_shift_hom T r X hX h)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp]

end CategoryTheory.Stabilization
