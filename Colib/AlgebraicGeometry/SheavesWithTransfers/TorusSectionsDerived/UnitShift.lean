/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived

/-!
# The shift of the actual derived torus unit

The canonical shift structure of total derived torus sections is
defined using the transported homotopy unit. Transporting it back
through the original quotient gives shift compatibility for the
literal cochain comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u w

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

local notation "B" => torusSectionsFunctor k
local notation "R" => torusSectionsDerivedFunctor k
local notation "η" => torusSectionsDerivedUnit k

private theorem commShift_of_unit_transport
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (q : C ⥤ D) (F : D ⥤ E) (G : D ⥤ E)
    [q.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
    (β : F ⟶ G) [NatTrans.CommShift β ℤ]
    {F' G' : C ⥤ E} [F'.CommShift ℤ] [G'.CommShift ℤ]
    (e₁ : F' ≅ q ⋙ F) (e₂ : q ⋙ G ≅ G')
    [NatTrans.CommShift e₁.hom ℤ] [NatTrans.CommShift e₂.hom ℤ]
    (α : F' ⟶ G') (h : α = e₁.hom ≫ Functor.whiskerLeft q β ≫ e₂.hom) :
    NatTrans.CommShift α ℤ := by
  subst α
  infer_instance

private theorem homotopySourceShift
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (F : A ⥤ A) [F.Additive] :
    let c := ComplexShape.up ℤ
    let T := F.mapHomologicalComplex c
    let H := F.mapHomotopyCategory c
    let q := HomotopyCategory.quotient A c
    let Qh := DerivedCategory.Qh (C := A)
    let d := DerivedCategory.quotientCompQhIso A
    let a := F.mapHomotopyCategoryFactors c
    let e : T ⋙ DerivedCategory.Q ≅ q ⋙ (H ⋙ Qh) :=
      Functor.isoWhiskerLeft T d.symm ≪≫ (Functor.associator T q Qh).symm ≪≫
        Functor.isoWhiskerRight a.symm Qh ≪≫ Functor.associator q H Qh
    NatTrans.CommShift e.hom ℤ := by
  intro c T H q Qh d a e
  let u₁ := Functor.whiskerLeft T d.inv
  let u₂ := (Functor.associator T q Qh).inv
  let u₃ := Functor.whiskerRight a.inv Qh
  let u₄ := (Functor.associator q H Qh).hom
  let : NatTrans.CommShift d.hom ℤ := inferInstance
  let : NatTrans.CommShift a.hom ℤ := inferInstance
  let : NatTrans.CommShift d.inv ℤ := inferInstance
  let : NatTrans.CommShift a.inv ℤ := inferInstance
  let : NatTrans.CommShift u₁ ℤ := inferInstanceAs
    (NatTrans.CommShift (Functor.whiskerLeft T d.inv) ℤ)
  let : NatTrans.CommShift u₂ ℤ := inferInstanceAs
    (NatTrans.CommShift (Functor.associator T q Qh).inv ℤ)
  let : NatTrans.CommShift u₃ ℤ := inferInstanceAs
    (NatTrans.CommShift (Functor.whiskerRight a.inv Qh) ℤ)
  let : NatTrans.CommShift u₄ ℤ := inferInstanceAs
    (NatTrans.CommShift (Functor.associator q H Qh).hom ℤ)
  change NatTrans.CommShift (u₁ ≫ u₂ ≫ u₃ ≫ u₄) ℤ
  infer_instance

/-- The genuine cochain comparison commutes with the signed shift. -/
instance torusSectionsDerivedUnit_commShift : NatTrans.CommShift (η) ℤ := by
  let A := SheafWithTransfers.{u + 1} k
  let c := ComplexShape.up ℤ
  let q := HomotopyCategory.quotient A c
  let Qh := DerivedCategory.Qh (C := A)
  let D := DerivedCategory.Q (C := A)
  let F := (B).mapHomologicalComplex c
  let H := (B).mapHomotopyCategory c
  let a := (B).mapHomotopyCategoryFactors c
  let d := DerivedCategory.quotientCompQhIso A
  let β := Stacks.Injectives.homotopyUnitOfComplexUnit B R η
  let : NatTrans.CommShift β ℤ :=
    Functor.IsRightDerivedFunctor.natTrans_commShift (R) β (HomotopyCategory.quasiIso A c) ℤ
  let e₁ : F ⋙ D ≅ q ⋙ (H ⋙ Qh) :=
    Functor.isoWhiskerLeft F d.symm ≪≫ (Functor.associator F q Qh).symm ≪≫
      Functor.isoWhiskerRight a.symm Qh ≪≫ Functor.associator q H Qh
  let e₂ : q ⋙ (Qh ⋙ R) ≅ D ⋙ R :=
    (Functor.associator q Qh R).symm ≪≫ Functor.isoWhiskerRight d R
  let τ := Functor.whiskerLeft q β
  have h : (η) = e₁.hom ≫ τ ≫ e₂.hom := by
    apply NatTrans.ext
    funext K
    have ha : a.inv.app K = 𝟙 _ := by
      have h := Functor.mapHomotopyCategoryFactors_hom_app (B) K
      apply (cancel_mono (a.hom.app K)).1
      exact (a.inv_hom_id_app K).trans
        ((congrArg (𝟙 _ ≫ ·) h).trans (Category.id_comp _)).symm
    have he₁ : e₁.hom.app K = d.inv.app (F.obj K) := by
      let X := (F ⋙ q).obj K
      change d.inv.app (F.obj K) ≫
          (𝟙 (Qh.obj X) ≫ (Qh.map (a.inv.app K) ≫ 𝟙 (Qh.obj X))) = _
      have hm : Qh.map (a.inv.app K) = 𝟙 (Qh.obj X) :=
        (Qh.congr_map ha).trans (Qh.map_id X)
      let j := d.inv.app (F.obj K)
      let z := 𝟙 (Qh.obj X)
      change j ≫ z ≫ Qh.map (a.inv.app K) ≫ z = j
      calc
        _ = j ≫ z ≫ z ≫ z := congrArg (fun f => j ≫ z ≫ f ≫ z) hm
        _ = j := by
          change j ≫ 𝟙 (Qh.obj X) ≫ 𝟙 (Qh.obj X) ≫ 𝟙 (Qh.obj X) = j
          exact (congrArg (j ≫ ·) ((congrArg (𝟙 (Qh.obj X) ≫ ·)
            (Category.id_comp (𝟙 (Qh.obj X)))).trans (Category.id_comp _))).trans
            (Category.comp_id j)
    have he₂ : e₂.hom.app K = (R).map (d.hom.app K) := Category.id_comp _
    have ht : β.app (q.obj K) =
        d.hom.app (F.obj K) ≫ (η).app K ≫ (R).map (d.inv.app K) :=
      Stacks.Injectives.homotopyUnitOfComplexUnit_app_quotient B R η K
    change (η).app K = e₁.hom.app K ≫ β.app (q.obj K) ≫ e₂.hom.app K
    rw [he₁, he₂, ht]
    have hh : (R).map (d.inv.app K) ≫ (R).map (d.hom.app K) = 𝟙 ((R).obj (D.obj K)) :=
      ((R).map_comp _ _).symm.trans
        (((R).congr_map (d.inv_hom_id_app K)).trans ((R).map_id _))
    symm
    calc
      _ = d.inv.app (F.obj K) ≫ d.hom.app (F.obj K) ≫ (η).app K ≫
          (R).map (d.inv.app K) ≫ (R).map (d.hom.app K) := by
        simp only [Category.assoc]
      _ = (η).app K ≫ ((R).map (d.inv.app K) ≫ (R).map (d.hom.app K)) :=
        d.inv_hom_id_app_assoc (F.obj K) _
      _ = _ := (congrArg ((η).app K ≫ ·) hh).trans (Category.comp_id _)
  let : NatTrans.CommShift e₁.hom ℤ := homotopySourceShift (B)
  let u := (Functor.associator q Qh R).inv
  let v := Functor.whiskerRight d.hom R
  let : NatTrans.CommShift u ℤ := inferInstanceAs
    (NatTrans.CommShift (Functor.associator q Qh R).inv ℤ)
  let : NatTrans.CommShift v ℤ := inferInstanceAs
    (NatTrans.CommShift (Functor.whiskerRight d.hom R) ℤ)
  let : NatTrans.CommShift e₂.hom ℤ := inferInstanceAs (NatTrans.CommShift (u ≫ v) ℤ)
  exact commShift_of_unit_transport q (H ⋙ Qh) (Qh ⋙ R) β e₁ e₂ (η) h

end AlgebraicGeometry.SheafWithTransfers
