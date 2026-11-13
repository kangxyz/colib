/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Total
import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso

/-!
# Singular totalization of a coefficient in one degree

The bicomplex of a single coefficient is its original singular complex
placed in the corresponding column. The native total comparison uses
the differential sign of that column.
-/

public noncomputable section

open CategoryTheory HomologicalComplex₂
open StacksDraft.TotalComplexQuasiIso

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "c" => ComplexShape.up ℤ

/-- The actual singular bicomplex of a single coefficient is concentrated
in that coefficient degree. -/
def singularBicomplexSingleIso (P : PresheafWithTransfers.{v} k) (a : ℤ) :
    (singularBicomplexFunctor k).obj
        ((CochainComplex.singleFunctor (PresheafWithTransfers.{v} k) a).obj P) ≅
      singleColumn (singularCochainComplex P 0) a := by
  let F : PresheafWithTransfers.{v} k ⥤ CochainComplex (PresheafWithTransfers.{v} k) ℤ :=
    singularCochainFunctor 0
  exact (HomologicalComplex.singleMapHomologicalComplex F c a).app P

/-- Singular totalization of a coefficient placed at degree `a` is its
original singular complex shifted by `-a`. -/
def singularTotalSingleIso (P : PresheafWithTransfers.{v} k) (a : ℤ) :
    (singularTotalFunctor k).obj
        ((CochainComplex.singleFunctor (PresheafWithTransfers.{v} k) a).obj P) ≅
      (singularCochainComplex P 0)⟦-a⟧ := by
  let f := totalSingleColumnUnit (singularCochainComplex P 0) a
  let : IsIso f := isIso_totalSingleColumnUnit (singularCochainComplex P 0) a
  exact HomologicalComplex₂.total.mapIso (singularBicomplexSingleIso P a) c ≪≫ (asIso f).symm

/-- In degree zero the single-column comparison lands in the original
unshifted singular complex. -/
def singularTotalSingleZeroIso (P : PresheafWithTransfers.{v} k) :
    (singularTotalFunctor k).obj
        ((CochainComplex.singleFunctor (PresheafWithTransfers.{v} k) 0).obj P) ≅
      singularCochainComplex P 0 :=
  singularTotalSingleIso P 0 ≪≫
    (shiftFunctorZero' (CochainComplex (PresheafWithTransfers.{v} k) ℤ) (-(0 : ℤ)) (by simp)).app _

private theorem singularBicomplexSingleIso_hom_zero_zero (P : PresheafWithTransfers.{v} k) :
    ((singularBicomplexSingleIso P 0).hom.f 0).f 0 =
      ((singularCochainFunctor 0).map (HomologicalComplex.singleObjXSelf c 0 P).hom).f 0 ≫
        (HomologicalComplex.singleObjXSelf c 0 (singularCochainComplex P 0)).inv.f 0 := by
  let A := PresheafWithTransfers.{v} k
  let F : A ⥤ CochainComplex A ℤ := singularCochainFunctor 0
  let t := HomologicalComplex.singleMapHomologicalComplex F c (0 : ℤ)
  let E := HomologicalComplex.eval A c (0 : ℤ)
  have ht := HomologicalComplex.singleMapHomologicalComplex_hom_app_self F c (0 : ℤ) P
  exact E.congr_map ht

/-- The total degree-zero augmentation is the original single-coefficient map. -/
theorem singularTotalSingleZeroIso_unit (P : PresheafWithTransfers.{v} k) :
    singularTotalUnitApp k ((CochainComplex.singleFunctor (PresheafWithTransfers.{v} k) 0).obj P) ≫
      (singularTotalSingleZeroIso P).hom = singularCochainUnitApp P := by
  let A := PresheafWithTransfers.{v} k
  let K := (CochainComplex.singleFunctor A 0).obj P
  let W := singularCochainComplex P 0
  let B := (singularBicomplexFunctor k).obj K
  let D := singleColumn W 0
  let e := singularBicomplexSingleIso P 0
  let g : (singularTotalFunctor k).obj K ⟶ D.total c := HomologicalComplex₂.total.map e.hom c
  let f := totalSingleColumnUnit W 0
  let : IsIso f := isIso_totalSingleColumnUnit W 0
  let z := (shiftFunctorZero' (CochainComplex A ℤ) (-(0 : ℤ)) (by simp)).app W
  have h₀ : z.inv.f 0 = 𝟙 (W.X 0) := by
    change ((shiftFunctorZero (CochainComplex A ℤ) ℤ).inv.app W).f 0 = _
    rw [CochainComplex.shiftFunctorZero_inv_app_f]
    rfl
  have h : singularTotalUnitApp k K ≫ g = singularCochainUnitApp P ≫ z.inv ≫ f := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f]
    let i : K.X 0 ⟶ (B.X 0).X 0 := singularZeroInclusion (K.X 0)
    let j := B.ιTotal c 0 0 0 (by decide)
    let t := D.ιTotal c 0 0 0 (by decide)
    let m : (B.total c).X 0 ⟶ (D.total c).X 0 := g.f 0
    let l := (e.hom.f 0).f 0
    change (i ≫ j) ≫ m =
      (singularCochainUnitApp P).f 0 ≫ z.inv.f 0 ≫ f.f 0
    have hg : j ≫ m = l ≫ t := HomologicalComplex₂.ιTotal_map B D e.hom c 0 0 0 (by decide)
    have he : l = ((singularCochainFunctor 0).map
        (HomologicalComplex.singleObjXSelf c 0 P).hom).f 0 ≫
        ((HomologicalComplex.singleObjXSelf c 0 W).inv).f 0 :=
      singularBicomplexSingleIso_hom_zero_zero P
    let s := (HomologicalComplex.singleObjXSelf c 0 P).hom
    let v := (HomologicalComplex.singleObjXSelf c 0 W).inv.f 0
    let fs := ((singularCochainFunctor 0).map s).f 0
    have hs : i ≫ fs = s ≫ singularZeroInclusion P := (singularZeroInclusion_naturality s).symm
    calc
      _ = i ≫ j ≫ m := Category.assoc _ _ _
      _ = i ≫ l ≫ t := congrArg (i ≫ ·) hg
      _ = i ≫ (fs ≫ v) ≫ t := congrArg (fun a => i ≫ a ≫ t) he
      _ = (i ≫ fs) ≫ v ≫ t :=
        (congrArg (i ≫ ·) (Category.assoc fs v t)).trans (Category.assoc i fs _).symm
      _ = (s ≫ singularZeroInclusion P) ≫ v ≫ t := congrArg (· ≫ v ≫ t) hs
      _ = (s ≫ singularZeroInclusion P) ≫ f.f 0 := rfl
      _ = (singularCochainUnitApp P).f 0 ≫ f.f 0 :=
        congrArg (· ≫ f.f 0) (singularCochainUnitApp_f_zero P).symm
      _ = _ := by rw [h₀, Category.id_comp]
  change (singularTotalUnitApp k K ≫ g) ≫ inv f ≫ z.hom = _
  rw [h]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.PresheafWithTransfers
