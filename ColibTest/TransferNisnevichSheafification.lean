/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Sheafification

/-! # Consumers of actual transfer-preserving Nisnevich sheafification -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory
open AlgebraicGeometry
open Opposite
open _root_.AlgebraicGeometry.PresheafWithTransfers

universe u

namespace ColibTest.TransferNisnevichSheafification

variable (k : Type u) [Field k]
variable [HasWeakSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]

/-- The output satisfies the original ordinary smooth-site sheaf condition. -/
example (P : PresheafWithTransfers.{u + 1} k) :
    Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).obj ((nisnevichSheafify k).obj P).obj) :=
  ((nisnevichSheafify k).obj P).property

/-- Source-arrow additivity of the result, including negative multiplicities. -/
example (P : PresheafWithTransfers.{u + 1} k) {X Y : Cor k} (α β : X ⟶ Y) :
    transfer ((nisnevichSheafify k).obj P).obj (α - β) =
      transfer ((nisnevichSheafify k).obj P).obj α -
        transfer ((nisnevichSheafify k).obj P).obj β := transfer_sub _ α β

/-- The canonical unit is natural for arbitrary signed correspondences. -/
example (P : PresheafWithTransfers.{u + 1} k) {X Y : Cor k} (α : X ⟶ Y) :
    transfer P α ≫ (toNisnevichSheafify k P).hom.app (op X) =
      (toNisnevichSheafify k P).hom.app (op Y) ≫
        transfer ((nisnevichSheafify k).obj P).obj α :=
  transfer_naturality (toNisnevichSheafify k P) α

/-- Universal extension, with uniqueness in the transfer-natural category. -/
example (P : PresheafWithTransfers.{u + 1} k) (Q : SheafWithTransfers.{u + 1} k)
    (η : P ⟶ Q.obj) :
    ∃! γ : (nisnevichSheafify k).obj P ⟶ Q,
      toNisnevichSheafify k P ≫ γ.hom = η := by
  exact ⟨nisnevichSheafifyLift k η, toNisnevichSheafify_lift k η,
    fun γ hγ => nisnevichSheafifyLift_unique k η γ hγ⟩

example : nisnevichSheafify k ⊣ SheafWithTransfers.forget k :=
  nisnevichSheafificationAdjunction k

example (P : PresheafWithTransfers.{u + 1} k) :
    (nisnevichSheafificationAdjunction k).unit.app P = toNisnevichSheafify k P :=
  nisnevichSheafificationAdjunction_unit_app k P

example (Q : SheafWithTransfers.{u + 1} k) :
    IsIso (toNisnevichSheafify k Q.obj) := isIso_toNisnevichSheafify k Q.obj Q.property

end ColibTest.TransferNisnevichSheafification

namespace ColibTest.TransferNisnevichSheafification

/-- A usable functor over every field, with no sheafification or forgetful
compatibility assumptions supplied by the caller. -/
def actualSheafification (k : Type u) [Field k] :
    PresheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k :=
  nisnevichSheafify k

/-- The actual left adjunction discharges every universe-size instance at
coefficient universe `u + 1`, without assuming any transfer descent result. -/
def actualSheafificationAdjunction (k : Type u) [Field k] :
    actualSheafification k ⊣ SheafWithTransfers.forget k :=
  nisnevichSheafificationAdjunction k

/-- The result is genuine ordinary Nisnevich sheafification after forgetting
transfers, with all ordinary and correspondence hypotheses synthesized. -/
def actualUnderlyingComparison (k : Type u) [Field k] :
    toPresheaf k ⋙ presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1} ≅
    actualSheafification k ⋙ SheafWithTransfers.toSheaf k :=
  nisnevichSheafificationUnderlyingIso k

/-- The genuine ordinary comparison intertwines the two canonical units. -/
theorem actualUnderlyingComparison_unit (k : Type u) [Field k]
    (P : PresheafWithTransfers.{u + 1} k) :
    toSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P) ≫
      ((actualUnderlyingComparison k).hom.app P).hom =
        (toPresheaf k).map (toNisnevichSheafify k P) :=
  toSheafify_nisnevichSheafificationUnderlyingIso k P

/-- Under the inverse comparison, a section sent through the transfer unit
is exactly its image under ordinary sheafification. -/
theorem actualUnderlyingComparison_section (k : Type u) [Field k]
    (P : PresheafWithTransfers.{u + 1} k) (X : SmoothSite (Spec (.of k)))
    (s : sections P (Cor.mk X)) :
    (((actualUnderlyingComparison k).inv.app P).hom.app (op X))
      ((toNisnevichSheafify k P).hom.app (op (Cor.mk X)) s) =
    (toSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).obj P)).app (op X) s := by
  have h : (toPresheaf k).map (toNisnevichSheafify k P) ≫
      ((actualUnderlyingComparison k).inv.app P).hom =
      toSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P) := by
    let a : (toPresheaf k).obj P ⟶
        sheafify (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P) :=
      toSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P)
    let b : sheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((toPresheaf k).obj P) ⟶ (toPresheaf k).obj ((nisnevichSheafify k).obj P).obj :=
      ((actualUnderlyingComparison k).hom.app P).hom
    let c : (toPresheaf k).obj ((nisnevichSheafify k).obj P).obj ⟶
        sheafify (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P) :=
      ((actualUnderlyingComparison k).inv.app P).hom
    have hu := actualUnderlyingComparison_unit k P
    change a ≫ b = (toPresheaf k).map (toNisnevichSheafify k P) at hu
    have hi : b ≫ c = 𝟙 _ :=
      congrArg (fun f => f.hom) ((actualUnderlyingComparison k).hom_inv_id_app P)
    change (toPresheaf k).map (toNisnevichSheafify k P) ≫ c = a
    calc
      _ = (a ≫ b) ≫ c := congrArg (fun f : (toPresheaf k).obj P ⟶
        (toPresheaf k).obj ((nisnevichSheafify k).obj P).obj => f ≫ c) hu.symm
      _ = a ≫ (b ≫ c) := Category.assoc _ _ _
      _ = a := (congrArg (fun f => a ≫ f) hi).trans (Category.comp_id a)

  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op X)) s

end ColibTest.TransferNisnevichSheafification
