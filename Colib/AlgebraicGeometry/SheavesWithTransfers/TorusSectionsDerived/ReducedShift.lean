/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.ReducedTriangulated
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.UnitShift
import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.UnboundedLocalization
import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-!
# The reduced torus inclusion commutes with the native shift

The inclusion of the original split kernel is the derived
transformation of its literal inclusion on sheaves. The genuine
derived units therefore identify its shift compatibility.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open Stacks.Injectives

universe u w

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

local notation "N" => reducedTorusSectionsDerivedFunctor k
local notation "B" => torusSectionsDerivedFunctor k
local notation "ν" => reducedTorusSectionsDerivedUnit k
local notation "η" => torusSectionsDerivedUnit k
local notation "c" => ComplexShape.up ℤ

instance reducedTorusSectionsDerivedInclusion_commShift :
    NatTrans.CommShift (reducedTorusSectionsDerivedInclusion k) ℤ := by
  let A := SheafWithTransfers.{u + 1} k
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let q := HomotopyCategory.quotient A c
  let F := reducedTorusSectionsFunctor k
  let G := torusSectionsFunctor k
  let f := reducedTorusSectionsInclusion k
  let α := homotopyUnitOfComplexUnit F (N) (ν)
  let β := homotopyUnitOfComplexUnit G (B) (η)
  let W := HomotopyCategory.quasiIso A c
  let : (N).IsRightDerivedFunctor α W := inferInstanceAs
    ((N).IsRightDerivedFunctor (homotopyUnitOfComplexUnit F (N) (ν)) W)
  let : (B).IsRightDerivedFunctor β W := inferInstanceAs
    ((B).IsRightDerivedFunctor (homotopyUnitOfComplexUnit G (B) (η)) W)
  let τ := Functor.whiskerRight (f.mapHomotopyCategory c) DerivedCategory.Qh
  let j := reducedTorusSectionsDerivedInclusion k
  let : NatTrans.CommShift α ℤ :=
    Functor.IsRightDerivedFunctor.natTrans_commShift (N) α W ℤ
  let : NatTrans.CommShift β ℤ :=
    Functor.IsRightDerivedFunctor.natTrans_commShift (B) β W ℤ
  let : NatTrans.CommShift τ ℤ := inferInstanceAs
    (NatTrans.CommShift (Functor.whiskerRight (f.mapHomotopyCategory c) DerivedCategory.Qh) ℤ)
  have h : Functor.rightDerivedNatTrans (N) (B) α β W τ = j := by
    apply Functor.rightDerived_ext (N) α W
    apply NatTrans.ext
    funext X
    obtain ⟨I, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    let e := DerivedCategory.quotientCompQhIso A
    let J := ((F).mapHomologicalComplex c).obj I
    let K := ((G).mapHomologicalComplex c).obj I
    let g := (f.mapHomologicalComplex c).app I
    let t := e.inv.app I
    have hI : (ν).app I ≫ j.app (Q.obj I) = Q.map g ≫ (η).app I :=
      reducedTorusSectionsDerivedUnit_inclusion k I
    have hτ : τ.app (q.obj I) ≫ e.hom.app K = e.hom.app J ≫ Q.map g :=
      e.hom.naturality g
    have hj : (N).map t ≫ j.app (DerivedCategory.Qh.obj (q.obj I)) =
        j.app (Q.obj I) ≫ (B).map t := j.naturality t
    have hα : α.app (q.obj I) = e.hom.app J ≫ (ν).app I ≫ (N).map t :=
      homotopyUnitOfComplexUnit_app_quotient F (N) (ν) I
    have hβ : β.app (q.obj I) = e.hom.app K ≫ (η).app I ≫ (B).map t :=
      homotopyUnitOfComplexUnit_app_quotient G (B) (η) I
    change α.app (q.obj I) ≫ (Functor.rightDerivedNatTrans (N) (B) α β W τ).app
        (DerivedCategory.Qh.obj (q.obj I)) =
      α.app (q.obj I) ≫ j.app (DerivedCategory.Qh.obj (q.obj I))
    calc
      _ = τ.app (q.obj I) ≫ β.app (q.obj I) :=
        Functor.rightDerivedNatTrans_app (N) (B) α β W τ (q.obj I)
      _ = e.hom.app J ≫ Q.map g ≫ (η).app I ≫ (B).map t := by
        rw [hβ, ← Category.assoc, hτ, Category.assoc]
      _ = e.hom.app J ≫ (ν).app I ≫ j.app (Q.obj I) ≫ (B).map t := by
        rw [← Category.assoc (Q.map g), ← hI, Category.assoc]
      _ = _ := by
        rw [hα, Category.assoc, Category.assoc, hj]
  let ι := Functor.rightDerivedNatTrans (N) (B) α β W τ
  let : NatTrans.CommShift ι ℤ := Functor.rightDerivedNatTrans_commShift (N) (B) α β W ℤ τ
  exact NatTrans.commShift_of_eq (show j = ι from h.symm)

end AlgebraicGeometry.SheafWithTransfers
