/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedAdjunction
import StacksFrontier.Homology.Injectives.DerivedCategory.RightDerivedTriangulated

/-!
# The derived torus comparison on injective cochains

The native comparison on K-injective homotopy representatives agrees
with the actual exact reindexing of the derived forget unit on cochains.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u w₁ w₂

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w₁} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w₂} (SheafWithTransfers.{u + 1} k)]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "c" => ComplexShape.up ℤ
local notation "T" => (withParameterFunctor Gₘ : PST ⥤ PST)
local notation "U" => (SheafWithTransfers.forget k : NST ⥤ PST)
local notation "R" => U ⋙ T

/-- The injective model uses the literal derived forget unit and the
exact reindexing factorization on cochains. -/
theorem torusTensorInjectiveReindexingIso_hom_app_quotient
    (I : CochainComplex NST ℤ) [hI : I.IsKInjective] :
    let J : TorusTensorInjectiveHomotopy k := ⟨(HomotopyCategory.quotient NST c).obj I, hI⟩
    (DerivedCategory.quotientCompQhIso PST).inv.app (((R).mapHomologicalComplex c).obj I) ≫
        (torusTensorInjectiveReindexingIso k).hom.app J ≫
        (torusTensorDerivedRight k).map ((DerivedCategory.quotientCompQhIso NST).hom.app I) =
      (T).mapDerivedCategoryFactors.inv.app (((U).mapHomologicalComplex c).obj I) ≫
        (T).mapDerivedCategory.map ((forgetDerivedUnit k).app I) := by
  intro J
  let V := ((U).mapHomologicalComplex c).obj I
  let q := HomotopyCategory.quotient PST c
  let E := (T).mapDerivedCategory
  let d := (DerivedCategory.quotientCompQhIso PST).app V
  let e := (DerivedCategory.quotientCompQhIso PST).app (((T).mapHomologicalComplex c).obj V)
  let j := (DerivedCategory.quotientCompQhIso NST).app I
  let f := (T).mapDerivedCategoryFactors.app V
  let g := (T).mapDerivedCategoryFactorsh.app (q.obj V)
  let a := (forgetDerivedUnit k).app I
  let b := Stacks.Injectives.homotopyUnitOfComplexUnit U (forgetDerivedFunctor k)
    (forgetDerivedUnit k)
  have hb : b.app J.obj = d.hom ≫ a ≫ (forgetDerivedFunctor k).map j.inv :=
    Stacks.Injectives.homotopyUnitOfComplexUnit_app_quotient U (forgetDerivedFunctor k)
      (forgetDerivedUnit k) I
  have hg : g.hom = E.map d.hom ≫ f.hom ≫ e.inv := by
    let Q := DerivedCategory.Qh (C := PST)
    let m := ((T).mapHomotopyCategoryFactors c).inv.app V
    have hf : g.hom = E.map d.hom ≫ f.hom ≫ e.inv ≫ Q.map m :=
      (T).mapDerivedCategoryFactorsh_hom_app V
    have hm : Q.map m = 𝟙 _ := Q.map_id _
    exact hf.trans (congrArg (E.map d.hom ≫ f.hom ≫ ·)
      ((congrArg (e.inv ≫ ·) hm).trans (Category.comp_id e.inv)))
  have hge : e.inv ≫ g.inv ≫ E.map d.hom = f.inv := by
    apply (cancel_mono (f.hom ≫ e.inv)).1
    simp only [Category.assoc, ← hg, g.inv_hom_id, f.inv_hom_id_assoc]
    exact Category.comp_id e.inv
  have hα : (torusTensorInjectiveReindexingIso k).hom.app J = g.inv ≫ E.map (b.app J.obj) := by
    unfold torusTensorInjectiveReindexingIso
    simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app, asIso_hom]
    change DerivedCategory.Qh.map (𝟙 _) ≫ g.inv ≫ E.map (b.app J.obj) = _
    rw [(DerivedCategory.Qh (C := PST)).map_id]
    exact Category.id_comp _
  change e.inv ≫ (torusTensorInjectiveReindexingIso k).hom.app J ≫
    E.map ((forgetDerivedFunctor k).map j.hom) = f.inv ≫ E.map a
  have ha : E.map ((forgetDerivedFunctor k).map j.inv) ≫
      E.map ((forgetDerivedFunctor k).map j.hom) = 𝟙 _ := by
    rw [← E.map_comp, ← (forgetDerivedFunctor k).map_comp, j.inv_hom_id,
      (forgetDerivedFunctor k).map_id, E.map_id]
  rw [hα, hb]
  simp only [E.map_comp, Category.assoc, ha, reassoc_of% hge]
  exact congrArg (f.inv ≫ ·) (Category.comp_id (E.map a))

end AlgebraicGeometry.SheafWithTransfers
