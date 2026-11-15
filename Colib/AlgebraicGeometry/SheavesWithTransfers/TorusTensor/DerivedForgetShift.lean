/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedAdjunction
public import StacksFrontier.Homology.Injectives.DerivedCategory.RightDerivedTriangulated

/-! # The shift of the derived underlying presheaf functor -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u w w'

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "NST" => LargeSheaves k
local notation "R" => forgetDerivedFunctor k
local notation "U" => SheafWithTransfers.forget k
local notation "c" => ComplexShape.up ℤ

/-- The abelian structure on transfer sheaves for the derived forgetful shift. -/
local instance : Abelian NST := SheafWithTransfers.abelian k

/-- Derived forget carries the shift of the actual homotopy-level derived unit. -/
instance forgetDerivedFunctorCommShift : (R).CommShift ℤ :=
  Stacks.Injectives.commShiftOfComplexUnit U (R) (forgetDerivedUnit k)

/-- The unit of the original homotopy-level forget construction preserves shift. -/
instance forgetHomotopyUnitCommShift : NatTrans.CommShift (forgetHomotopyUnit k) ℤ := by
  let : (R).IsRightDerivedFunctor (forgetHomotopyUnit k) (HomotopyCategory.quasiIso NST c) :=
    Stacks.Injectives.isRightDerivedFunctor_homotopyUnitOfComplexUnit U (R) (forgetDerivedUnit k)
  exact Functor.IsRightDerivedFunctor.natTrans_commShift (R) (forgetHomotopyUnit k)
    (HomotopyCategory.quasiIso NST c) ℤ

local notation "PST" => LargePresheaves k
local notation "K₀" => CochainComplex NST ℤ
local notation "Qₛ" => (DerivedCategory.Q : K₀ ⥤ DerivedCategory NST)
local notation "Qₚ" => (DerivedCategory.Q : CochainComplex PST ℤ ⥤ DerivedCategory PST)

set_option maxHeartbeats 700000 in
-- Use the termwise comparison at every homotopy representative.
/-- The original comparison on cochains preserves the shift of derived forget. -/
theorem forgetDerivedUnit_commShift :
    NatTrans.CommShift (forgetDerivedUnit k) ℤ := by
  let q := HomotopyCategory.quotient NST c
  let e := DerivedCategory.quotientCompQhIso PST
  let d := DerivedCategory.quotientCompQhIso NST
  let F := U
  let L := F.mapHomotopyCategory c
  let B := F.mapHomologicalComplex c
  let Qhₚ : HomotopyCategory PST c ⥤ DerivedCategory PST := DerivedCategory.Qh
  let Qhₛ : HomotopyCategory NST c ⥤ DerivedCategory NST := DerivedCategory.Qh
  let qₚ := HomotopyCategory.quotient PST c
  let t := F.mapHomotopyCategoryFactors c
  let p₁ := Functor.isoWhiskerLeft B e.symm
  let p₂ := (Functor.associator B qₚ Qhₚ).symm
  let p₃ := Functor.isoWhiskerRight t.symm Qhₚ
  let p₄ := Functor.associator q L Qhₚ
  let r₁ := (Functor.associator q Qhₛ (R)).symm
  let r₂ := Functor.isoWhiskerRight d R
  let a₀ : B ⋙ Qₚ ≅ q ⋙ (L ⋙ Qhₚ) := p₁ ≪≫ p₂ ≪≫ p₃ ≪≫ p₄
  let b₀ : q ⋙ (Qhₛ ⋙ R) ≅ Qₛ ⋙ R := r₁ ≪≫ r₂
  let v := forgetHomotopyUnit k
  have h : forgetDerivedUnit k = a₀.hom ≫ Functor.whiskerLeft q v ≫ b₀.hom := by
    apply NatTrans.ext
    funext I
    have hv := Stacks.Injectives.homotopyUnitOfComplexUnit_app_quotient F R
      (forgetDerivedUnit k) I
    change v.app (q.obj I) = e.hom.app (B.obj I) ≫
      (forgetDerivedUnit k).app I ≫ (R).map (d.inv.app I) at hv
    change (forgetDerivedUnit k).app I =
      (e.inv.app (B.obj I) ≫ 𝟙 _ ≫ DerivedCategory.Qh.map
        ((F.mapHomotopyCategoryFactors c).inv.app I) ≫ 𝟙 _) ≫
        v.app (q.obj I) ≫ 𝟙 _ ≫ (R).map (d.hom.app I)
    have hid : DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors c).inv.app I) = 𝟙 _ :=
      DerivedCategory.Qh.map_id _
    rw [hid]
    let θ := (forgetDerivedUnit k).app I
    let d₀ := (R).mapIso (d.app I)
    let e₀ := e.app (B.obj I)
    have hθ : e₀.inv ≫ (e₀.hom ≫ θ ≫ d₀.inv) ≫ d₀.hom = θ := by
      rw [Category.assoc, Category.assoc, e₀.inv_hom_id_assoc, d₀.inv_hom_id]
      exact Category.comp_id θ
    have ht : θ = e₀.inv ≫ v.app (q.obj I) ≫ d₀.hom := by
      rw [hv]
      exact hθ.symm
    calc
      θ = e₀.inv ≫ v.app (q.obj I) ≫ d₀.hom := ht
      _ = _ := by
        let u := v.app (q.obj I)
        let X := (qₚ ⋙ Qhₚ).obj (B.obj I)
        let Y := (Qhₛ ⋙ R).obj (q.obj I)
        let z : Y ⟶ (Qₛ ⋙ R).obj I := d₀.hom
        change e₀.inv ≫ u ≫ z =
          (e₀.inv ≫ 𝟙 X ≫ 𝟙 X ≫ 𝟙 X) ≫ u ≫ 𝟙 Y ≫ z
        have h₁ : 𝟙 X ≫ 𝟙 X ≫ 𝟙 X = 𝟙 X := by
          simp only [Category.id_comp]
        rw [h₁]
        exact (congrArg₂ (· ≫ ·) (Category.comp_id e₀.inv)
          (congrArg (u ≫ ·) (Category.id_comp z))).symm
  rw [h]
  let : NatTrans.CommShift e.symm.hom ℤ := NatTrans.CommShift.of_iso_inv e ℤ
  let : NatTrans.CommShift t.symm.hom ℤ := NatTrans.CommShift.of_iso_inv t ℤ
  let : NatTrans.CommShift p₁.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift (Functor.whiskerLeft B e.symm.hom) ℤ)
  let : NatTrans.CommShift p₃.hom ℤ :=
    NatTrans.CommShift.whiskerRight t.symm.hom Qhₚ ℤ
  let : NatTrans.CommShift p₄.hom ℤ := NatTrans.CommShift.associator L Qhₚ ℤ
  let : NatTrans.CommShift (Functor.associator B qₚ Qhₚ).hom ℤ :=
    NatTrans.CommShift.associator qₚ Qhₚ ℤ
  let : NatTrans.CommShift p₂.hom ℤ :=
    NatTrans.CommShift.of_iso_inv (Functor.associator B qₚ Qhₚ) ℤ
  let : NatTrans.CommShift (Functor.associator q Qhₛ (R)).hom ℤ :=
    NatTrans.CommShift.associator Qhₛ R ℤ
  let : NatTrans.CommShift r₁.hom ℤ :=
    NatTrans.CommShift.of_iso_inv (Functor.associator q Qhₛ (R)) ℤ
  let : NatTrans.CommShift r₂.hom ℤ := NatTrans.CommShift.whiskerRight d.hom R ℤ
  let : NatTrans.CommShift b₀.hom ℤ := NatTrans.CommShift.comp r₁.hom r₂.hom ℤ
  let : NatTrans.CommShift v ℤ := forgetHomotopyUnitCommShift k
  let : NatTrans.CommShift (Functor.whiskerLeft q v) ℤ :=
    inferInstanceAs (NatTrans.CommShift (Functor.whiskerLeft q (forgetHomotopyUnit k)) ℤ)
  let : NatTrans.CommShift (p₃ ≪≫ p₄).hom ℤ :=
    NatTrans.CommShift.comp p₃.hom p₄.hom ℤ
  let : NatTrans.CommShift (p₂ ≪≫ p₃ ≪≫ p₄).hom ℤ :=
    NatTrans.CommShift.comp p₂.hom (p₃ ≪≫ p₄).hom ℤ
  let : NatTrans.CommShift a₀.hom ℤ :=
    NatTrans.CommShift.comp p₁.hom (p₂ ≪≫ p₃ ≪≫ p₄).hom ℤ
  let : NatTrans.CommShift (Functor.whiskerLeft q v ≫ b₀.hom) ℤ :=
    NatTrans.CommShift.comp (Functor.whiskerLeft q v) b₀.hom ℤ
  exact NatTrans.CommShift.comp a₀.hom (Functor.whiskerLeft q v ≫ b₀.hom) ℤ

end AlgebraicGeometry.SheafWithTransfers
