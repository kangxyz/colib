/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Shift.CommShiftTwo
import Mathlib.CategoryTheory.EssentialImage
public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift

/-!
# Descent of middle shift compatibility of the associator

A strong monoidal functor carries the shift compatibility of the middle
variable to its target if its tensorators commute with the shift.
For an essentially surjective functor the compatibility then holds on
every triple of target objects.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory Functor

universe u v u' v'

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The associator as a natural isomorphism in the middle variable. -/
def middleAssociatorIso (A L : C) : tensorRight L ⋙ tensorLeft A ≅
    tensorLeft A ⋙ tensorRight L :=
  (NatIso.ofComponents (fun X => α_ A X L) (fun f => associator_naturality_middle A f L)).symm

section Shift

variable [HasShift C ℤ] [∀ A : C, (tensorLeft A).CommShift ℤ]
  [∀ A : C, (tensorRight A).CommShift ℤ]

/-- A shift-compatible middle associator, written using the chosen two one-variable shifts. -/
def MiddleAssociatorCommShift (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [HasShift C ℤ] [∀ A : C, (tensorLeft A).CommShift ℤ]
    [∀ A : C, (tensorRight A).CommShift ℤ] : Prop :=
  ∀ A L : C, NatTrans.CommShift (middleAssociatorIso A L).hom ℤ

variable (C)

/-- Compatibility can be checked directly on the two component shift isomorphisms. -/
theorem middleAssociatorCommShift_iff :
    MiddleAssociatorCommShift C ↔ ∀ (A X L : C) (n : ℤ),
      (α_ A (X⟦n⟧) L).hom ≫
        A ◁ ((tensorRight L).commShiftIso n).hom.app X ≫
          ((tensorLeft A).commShiftIso n).hom.app (X ⊗ L) =
        ((tensorLeft A).commShiftIso n).hom.app X ▷ L ≫
          ((tensorRight L).commShiftIso n).hom.app (A ⊗ X) ≫
            (α_ A X L).hom⟦n⟧' := by
  constructor
  · intro H A X L n
    let := H A L
    let := NatTrans.CommShift.of_iso_inv (middleAssociatorIso A L) ℤ
    have h := NatTrans.shift_app_comm (middleAssociatorIso A L).inv n X
    simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
      Iso.symm_inv, NatIso.ofComponents_hom_app, middleAssociatorIso, Category.assoc] at h
    exact h.symm
  · intro H A L
    have h : NatTrans.CommShift (middleAssociatorIso A L).inv ℤ := by
      refine ⟨fun n => NatTrans.ext (funext fun X => ?_)⟩
      simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
        middleAssociatorIso, Iso.symm_inv, NatIso.ofComponents_hom_app, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
      exact (H A X L n).symm
    let : NatTrans.CommShift (middleAssociatorIso A L).symm.hom ℤ := h
    exact NatTrans.CommShift.of_iso_inv (middleAssociatorIso A L).symm ℤ

end Shift

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  [HasShift C ℤ] [∀ A : C, (tensorLeft A).CommShift ℤ]
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [HasShift D ℤ] [∀ A : D, (tensorLeft A).CommShift ℤ]
  [∀ A : D, (tensorRight A).CommShift ℤ]
  [TensorCommShift D ℤ]
  (Q : C ⥤ D) [Q.Monoidal] [Q.CommShift ℤ] [Functor.LaxMonoidal.CommShift Q ℤ]

omit [TensorCommShift D ℤ] in
/-- The actual associator and the two componentwise monoidal comparisons form a commuting
diagram after restricting the varied middle argument along a strong monoidal functor. -/
private theorem middleAssociator_descent_image (h : MiddleAssociatorCommShift C)
    (A L : C) :
    NatTrans.CommShift (Functor.whiskerLeft Q (middleAssociatorIso (Q.obj A) (Q.obj L)).hom) ℤ := by
  let R := tensorRight L
  let P := tensorLeft A
  let R' := tensorRight (Q.obj L)
  let P' := tensorLeft (Q.obj A)
  let eR := Functor.Monoidal.commTensorRight Q L
  let eP := Functor.Monoidal.commTensorLeft Q A
  let hR : NatTrans.CommShift eR.hom ℤ := Functor.LaxMonoidal.CommShift.commShift_μNatTransFst L
  let hP : NatTrans.CommShift eP.hom ℤ := Functor.LaxMonoidal.CommShift.commShift_μNatTransSnd A
  let a := middleAssociatorIso A L
  let a' := middleAssociatorIso (Q.obj A) (Q.obj L)
  let := h A L
  let b : Q ⋙ (R' ⋙ P') ≅ (R ⋙ P) ⋙ Q :=
    (Functor.associator Q R' P').symm ≪≫ Functor.isoWhiskerRight eR P' ≪≫
      Functor.associator R Q P' ≪≫ Functor.isoWhiskerLeft R eP ≪≫
      (Functor.associator R P Q).symm
  let b' : Q ⋙ (P' ⋙ R') ≅ (P ⋙ R) ⋙ Q :=
    (Functor.associator Q P' R').symm ≪≫ Functor.isoWhiskerRight eP R' ≪≫
      Functor.associator P Q R' ≪≫ Functor.isoWhiskerLeft P eR ≪≫
      (Functor.associator P R Q).symm
  have hb : NatTrans.CommShift b.hom ℤ := by
    let := hR
    let := hP
    dsimp [b]
    infer_instance
  have hb' : NatTrans.CommShift b'.hom ℤ := by
    let := hR
    let := hP
    dsimp [b']
    infer_instance
  let h₀ := Functor.whiskerLeft Q a'.hom
  let h₁ := b.hom ≫ Functor.whiskerRight a.hom Q ≫ b'.inv
  have hEq : h₀ = h₁ := by
    apply NatTrans.ext
    funext X
    simp only [h₀, h₁, b, b', NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    let a₀ := (α_ (Q.obj A) (Q.obj X) (Q.obj L)).inv
    let u := Q.obj A ◁ (Functor.LaxMonoidal.μ Q X L)
    let v := Functor.LaxMonoidal.μ Q A (X ⊗ L)
    let w := Q.map (α_ A X L).inv
    let r := Functor.OplaxMonoidal.δ Q (A ⊗ X) L
    let t := Functor.OplaxMonoidal.δ Q A X ▷ Q.obj L
    change a₀ = 𝟙 _ ≫ u ≫ 𝟙 _ ≫ v ≫ 𝟙 _ ≫ w ≫ 𝟙 _ ≫ r ≫ t
    simp only [Category.id_comp]
    let r' := Functor.LaxMonoidal.μ Q (A ⊗ X) L
    let t' := (Functor.LaxMonoidal.μ Q A X) ▷ Q.obj L
    have hr : r ≫ t ≫ t' ≫ r' = 𝟙 _ := by
      have ht : t ≫ t' = 𝟙 _ := by
        change (Functor.OplaxMonoidal.δ Q A X ▷ Q.obj L) ≫
          (Functor.LaxMonoidal.μ Q A X ▷ Q.obj L) = 𝟙 _
        rw [← comp_whiskerRight, Functor.Monoidal.δ_μ, id_whiskerRight]
      rw [← Category.assoc t, ht, Category.id_comp]
      exact Functor.Monoidal.δ_μ Q (A ⊗ X) L
    apply (cancel_mono (t' ≫ r')).1
    simp only [Category.assoc, hr, Category.comp_id]
    exact (Functor.LaxMonoidal.associativity_inv Q A X L).symm
  change NatTrans.CommShift h₀ ℤ
  rw [hEq]
  let := hb
  let := hb'
  let : NatTrans.CommShift b'.inv ℤ := NatTrans.CommShift.of_iso_inv b' ℤ
  change NatTrans.CommShift (b.hom ≫ Functor.whiskerRight a.hom Q ≫ b'.inv) ℤ
  infer_instance

variable [Q.EssSurj]

include Q in
/-- A shift-compatible strong monoidal essentially surjective functor descends
the middle shift compatibility of the original associator. -/
theorem middleAssociatorCommShift_of_strongMonoidal
    (h : MiddleAssociatorCommShift C) : MiddleAssociatorCommShift D := by
  intro A L
  let a := Q.objObjPreimageIso A
  let l := Q.objObjPreimageIso L
  let A₀ := Q.objPreimage A
  let L₀ := Q.objPreimage L
  have h₀ : NatTrans.CommShift (middleAssociatorIso (Q.obj A₀) (Q.obj L₀)).hom ℤ := by
    let h' := middleAssociator_descent_image Q h A₀ L₀
    refine ⟨fun n => ?_⟩
    apply NatTrans.ext
    funext Y
    let X := Q.objPreimage Y
    let j := Q.objObjPreimageIso Y
    have hX := NatTrans.shift_app_comm
      (Functor.whiskerLeft Q (middleAssociatorIso (Q.obj A₀) (Q.obj L₀)).hom) n X
    simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
      Category.assoc, ← NatTrans.naturality_assoc] at hX
    let F := tensorRight (Q.obj L₀) ⋙ tensorLeft (Q.obj A₀)
    let G := tensorLeft (Q.obj A₀) ⋙ tensorRight (Q.obj L₀)
    let t := (middleAssociatorIso (Q.obj A₀) (Q.obj L₀)).hom
    have hm : (F.commShiftIso n).hom.app (Q.obj X) ≫ (t.app (Q.obj X))⟦n⟧' =
        t.app ((Q.obj X)⟦n⟧) ≫ (G.commShiftIso n).hom.app (Q.obj X) := by
      apply (cancel_epi (F.map ((Q.commShiftIso n).hom.app X))).1
      simp only [F, G, Functor.commShiftIso_comp_hom_app, Category.assoc]
      exact hX
    let α := (F.commShiftIso n).hom ≫ Functor.whiskerRight t (shiftFunctor D n)
    let β := Functor.whiskerLeft (shiftFunctor D n) t ≫ (G.commShiftIso n).hom
    change α.app Y = β.app Y
    apply (cancel_epi ((shiftFunctor D n ⋙ F).map j.hom)).1
    rw [α.naturality, β.naturality]
    exact congrArg (· ≫ (G ⋙ shiftFunctor D n).map j.hom) hm
  let qR := (curriedTensor D).flip.map l.inv
  let qP := (curriedTensor D).map a.inv
  let qR' := (curriedTensor D).flip.map l.hom
  let qP' := (curriedTensor D).map a.hom
  let t₀ := (middleAssociatorIso (Q.obj A₀) (Q.obj L₀)).hom
  let t := (middleAssociatorIso A L).hom
  let before : tensorRight L ⋙ tensorLeft A ⟶
      tensorRight (Q.obj L₀) ⋙ tensorLeft (Q.obj A₀) :=
    Functor.whiskerRight qR (tensorLeft A) ≫ Functor.whiskerLeft (tensorRight (Q.obj L₀)) qP
  let after : tensorLeft (Q.obj A₀) ⋙ tensorRight (Q.obj L₀) ⟶
      tensorLeft A ⋙ tensorRight L :=
    Functor.whiskerRight qP' (tensorRight (Q.obj L₀)) ≫
      Functor.whiskerLeft (tensorLeft A) qR'
  let := h₀
  have ht : t = before ≫ t₀ ≫ after := by
    apply NatTrans.ext
    funext X
    simp only [t, before, t₀, after, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc]
    change (α_ A X L).inv = A ◁ (X ◁ l.inv) ≫ a.inv ▷ (X ⊗ Q.obj L₀) ≫
      (α_ (Q.obj A₀) X (Q.obj L₀)).inv ≫ (a.hom ▷ X) ▷ Q.obj L₀ ≫ (A ⊗ X) ◁ l.hom
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
      ← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, id_whiskerRight,
      Category.id_comp, associator_inv_naturality_right_assoc, ← whiskerLeft_comp,
      Iso.inv_hom_id, whiskerLeft_id, Category.comp_id]
  change NatTrans.CommShift t ℤ
  rw [ht]
  change NatTrans.CommShift (before ≫ t₀ ≫ after) ℤ
  let : NatTrans.CommShift before ℤ := by dsimp [before, qP, qR]; infer_instance
  let : NatTrans.CommShift after ℤ := by dsimp [after, qP', qR']; infer_instance
  infer_instance

omit [Q.EssSurj] [TensorCommShift D ℤ] in
include Q in
/-- A faithful strong monoidal shift functor reflects compatibility of the middle associator
when both tensorators commute with shift. -/
theorem middleAssociatorCommShift_of_faithful
    [Q.Faithful] (h : MiddleAssociatorCommShift D) : MiddleAssociatorCommShift C := by
  intro A L
  let R := tensorRight L
  let P := tensorLeft A
  let R' := tensorRight (Q.obj L)
  let P' := tensorLeft (Q.obj A)
  let eR := Functor.Monoidal.commTensorRight Q L
  let eP := Functor.Monoidal.commTensorLeft Q A
  let hR : NatTrans.CommShift eR.hom ℤ := Functor.LaxMonoidal.CommShift.commShift_μNatTransFst L
  let hP : NatTrans.CommShift eP.hom ℤ := Functor.LaxMonoidal.CommShift.commShift_μNatTransSnd A
  let a := middleAssociatorIso A L
  let a' := middleAssociatorIso (Q.obj A) (Q.obj L)
  let := h (Q.obj A) (Q.obj L)
  let b : Q ⋙ (R' ⋙ P') ≅ (R ⋙ P) ⋙ Q :=
    (Functor.associator Q R' P').symm ≪≫ Functor.isoWhiskerRight eR P' ≪≫
      Functor.associator R Q P' ≪≫ Functor.isoWhiskerLeft R eP ≪≫
      (Functor.associator R P Q).symm
  let b' : Q ⋙ (P' ⋙ R') ≅ (P ⋙ R) ⋙ Q :=
    (Functor.associator Q P' R').symm ≪≫ Functor.isoWhiskerRight eP R' ≪≫
      Functor.associator P Q R' ≪≫ Functor.isoWhiskerLeft P eR ≪≫
      (Functor.associator P R Q).symm
  have hb : NatTrans.CommShift b.hom ℤ := by
    let := hR
    let := hP
    dsimp [b]
    infer_instance
  have hb' : NatTrans.CommShift b'.hom ℤ := by
    let := hR
    let := hP
    dsimp [b']
    infer_instance
  let h₀ := Functor.whiskerRight a.hom Q
  let h₁ := b.inv ≫ Functor.whiskerLeft Q a'.hom ≫ b'.hom
  have hEq : h₀ = h₁ := by
    apply NatTrans.ext
    funext X
    simp only [h₀, h₁, b, b', NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.assoc]
    let a₀ := (α_ (Q.obj A) (Q.obj X) (Q.obj L)).inv
    let u := Q.obj A ◁ (Functor.LaxMonoidal.μ Q X L)
    let v := Functor.LaxMonoidal.μ Q A (X ⊗ L)
    let w := Q.map (α_ A X L).inv
    let r := Functor.OplaxMonoidal.δ Q A (X ⊗ L)
    let t := Q.obj A ◁ Functor.OplaxMonoidal.δ Q X L
    let r' := Functor.LaxMonoidal.μ Q (A ⊗ X) L
    let t' := (Functor.LaxMonoidal.μ Q A X) ▷ Q.obj L
    change w = 𝟙 _ ≫ r ≫ t ≫ a₀ ≫ 𝟙 _ ≫ t' ≫ 𝟙 _ ≫ r' ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    have hr : u ≫ v ≫ r ≫ t = 𝟙 _ := by
      have ht : u ≫ t = 𝟙 _ := by
        change (Q.obj A ◁ Functor.LaxMonoidal.μ Q X L) ≫
          (Q.obj A ◁ Functor.OplaxMonoidal.δ Q X L) = 𝟙 _
        rw [← whiskerLeft_comp, Functor.Monoidal.μ_δ, whiskerLeft_id]
      simp only [v, r, Functor.Monoidal.μ_δ_assoc]
      exact ht
    apply (cancel_epi (u ≫ v)).1
    simp only [Category.assoc, reassoc_of% hr]
    exact Functor.LaxMonoidal.associativity_inv Q A X L
  refine NatTrans.CommShift.of_comp_faithful (G := Q) ?_
  change NatTrans.CommShift h₀ ℤ
  rw [hEq]
  let := hb
  let := hb'
  let : NatTrans.CommShift b.inv ℤ := NatTrans.CommShift.of_iso_inv b ℤ
  change NatTrans.CommShift (b.inv ≫ Functor.whiskerLeft Q a'.hom ≫ b'.hom) ℤ
  infer_instance

end CategoryTheory.MonoidalCategory
