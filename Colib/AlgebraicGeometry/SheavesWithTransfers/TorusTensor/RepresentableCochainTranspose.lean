/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.RepresentableUnit
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.SingularPlacement
import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# The torus transpose and the original singular augmentation

The original signed permutation commutes with augmentation because the
permutation followed by the simplex projection is the actual parameter
product of the simplex projection. Thus the coefficient transpose
remains the same map after forming singular complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme
open Stacks.DerivedIndexing

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "c" => ComplexShape.up ℤ
local notation "S" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject S
local notation "A" => nisnevichSheafify k
local notation "U" => (SheafWithTransfers.forget k : NST ⥤ PST)
local notation "T" => (withParameterFunctor Gₘ : PST ⥤ PST)
local notation "R" => U ⋙ T
local notation "sₚ" => CochainComplex.singleFunctor PST 0

/-- The actual torus and simplex permutation retains the original augmentation. -/
theorem singularCochainTorusParameterIso_unit (P : PST) :
    singularCochainUnitApp ((T).obj P) ≫ (singularCochainTorusParameterIso k P).hom =
      (HomologicalComplex.singleMapHomologicalComplex (T) c (0 : ℤ)).inv.app P ≫
        ((T).mapHomologicalComplex c).map (singularCochainUnitApp P) := by
  let e := ComplexShape.embeddingUpIntLE 0
  let K := singularComplex P
  let W := (withParameterSingularComplexIso P Gₘ).inv
  let g := mapExtendIso (T) e K
  let i := (singularCochainXIso ((T).obj P) 0 0)
  let j := (singularCochainXIso P 0 0)
  let j' := ((T).mapHomologicalComplex (.down ℕ)).obj K
  let d := j'.extendXIso e (show e.f 0 = (0 : ℤ) from rfl)
  have hu : singularTermUnit ((T).obj P) 0 ≫ W.f 0 = (T).map (singularTermUnit P 0) := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    let Z := X.unop.toSmoothSite
    let Δ := AlgebraicSimplex.smoothSiteObj k 0
    let γ := Cor.graphFunctor k
    let F := SmoothSite.productFst (SmoothSite.product Z Gₘ) Δ
    let p := SmoothSite.productFst Z Δ
    let σ := (SmoothSite.productSwapLastIso Z Δ Gₘ).inv
    change transfer P ((Cor.parameterProduct Gₘ).map (γ.map p)) ≫ transfer P (γ.map σ) =
      transfer P (γ.map F)
    rw [← transfer_comp, Cor.parameterProduct_graph, ← γ.map_comp]
    have hσ : σ ≫ SmoothSite.productSwapLast Z Δ Gₘ = 𝟙 _ :=
      (SmoothSite.productSwapLastIso Z Δ Gₘ).inv_hom_id
    have h : σ ≫ SmoothSite.productMap p (𝟙 Gₘ) = F := by
      calc
        _ = σ ≫ (SmoothSite.productSwapLast Z Δ Gₘ ≫ F) :=
          congrArg (σ ≫ ·) (SmoothSite.productSwapLast_fst Z Δ Gₘ).symm
        _ = (σ ≫ SmoothSite.productSwapLast Z Δ Gₘ) ≫ F := (Category.assoc _ _ _).symm
        _ = F := (congrArg (· ≫ F) hσ).trans (Category.id_comp F)
    exact congrArg (fun f => transfer P (γ.map f)) h
  have hW : ((e.extendFunctor PST).map W).f 0 = i.hom ≫ W.f 0 ≫ d.inv :=
    HomologicalComplex.extendMap_f W e (i := 0) (i' := 0) rfl
  have hg : g.hom.f 0 = d.hom ≫ (T).map j.inv :=
    mapExtendIso_hom_f_eq (T) e K (i := 0) (i' := 0) rfl
  apply HomologicalComplex.from_single_hom_ext
  change ((singularCochainUnitApp ((T).obj P)).f 0 ≫
      (((e.extendFunctor PST).map W).f 0 ≫ g.hom.f 0)) =
    ((HomologicalComplex.singleMapHomologicalComplex (T) c (0 : ℤ)).inv.app P).f 0 ≫
      (T).map ((singularCochainUnitApp P).f 0)
  let s := (HomologicalComplex.singleObjXSelf c (0 : ℤ) ((T).obj P)).hom
  let s' := HomologicalComplex.singleObjXSelf c (0 : ℤ) P
  let m := singularTermUnit ((T).obj P) 0
  let n := singularTermUnit P 0
  have h₁ : ((singularCochainUnitApp ((T).obj P)).f 0) = s ≫ m ≫ i.inv :=
    singularCochainUnitApp_f_zero ((T).obj P)
  have h₂ : ((singularCochainUnitApp P).f 0) = s'.hom ≫ n ≫ j.inv :=
    singularCochainUnitApp_f_zero P
  have h₃ : ((HomologicalComplex.singleMapHomologicalComplex (T) c (0 : ℤ)).inv.app P).f 0 =
      s ≫ (T).map s'.inv :=
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self (T) c (0 : ℤ) P
  rw [h₁, h₂, h₃, hW, hg]
  calc
    _ = s ≫ (m ≫ W.f 0) ≫ (T).map j.inv := by
      simp only [Category.assoc, i.inv_hom_id_assoc, d.inv_hom_id_assoc]
    _ = s ≫ (T).map n ≫ (T).map j.inv := by
      change s ≫ (singularTermUnit ((T).obj P) 0 ≫ W.f 0) ≫ (T).map j.inv = _
      rw [hu]
    _ = (s ≫ (T).map s'.inv) ≫ (T).map (s'.hom ≫ n ≫ j.inv) := by
      have hz : (T).map s'.inv ≫ (T).map s'.hom = 𝟙 _ := by
        rw [← (T).map_comp, s'.inv_hom_id]
        exact (T).map_id _
      simp only [Category.assoc, (T).map_comp, reassoc_of% hz]

/-- Forgetting the sheaf condition identifies the actual torus sheafification
comparison with the reindexed original sheafification unit. -/
theorem forget_torusSectionsSheafificationComplexMap_unit (K : CochainComplex PST ℤ) :
    ((Adjunction.mapHomologicalComplexAdjunction
        (nisnevichSheafificationAdjunction k) c).unit.app
          (((T).mapHomologicalComplex c).obj K)) ≫
      ((U).mapHomologicalComplex c).map (torusSectionsSheafificationComplexMap k c K) =
    ((T).mapHomologicalComplex c).map ((Adjunction.mapHomologicalComplexAdjunction
      (nisnevichSheafificationAdjunction k) c).unit.app K) := by
  ext i : 1
  change (nisnevichSheafificationAdjunction k).unit.app (torusSections (K.X i)) ≫
      ((torusSectionsSheafificationComplexMap k c K).f i).hom =
    (T).map ((nisnevichSheafificationAdjunction k).unit.app (K.X i))
  rw [nisnevichSheafificationAdjunction_unit_app, nisnevichSheafificationAdjunction_unit_app]
  exact torusSectionsSheafificationComplexMap_unit k c K i

/-- The actual transpose before localization is the source augmentation
followed by the original cancellation map and the sheafification unit. -/
theorem torusTensorRepresentableCochainTranspose (Y : Cor k) :
    let P := (representableLarge k).obj Y
    let C := torusCancellationCoefficients k Y
    let h := torusTensorRepresentableTargetAugmentation k Y
    let V := (U).mapHomologicalComplex c
    let a := (A).mapHomologicalComplex c
    let η := (Adjunction.mapHomologicalComplexAdjunction
      (nisnevichSheafificationAdjunction k) c).unit
    (torusTensorCochainAdjunction k).homEquiv ((sₚ).obj P)
        (singularSheafCochainComplex k C 0) (torusTensorRepresentableSingleQuotient k Y ≫ h) =
      η.app ((sₚ).obj P) ≫ V.map
        (a.map (singularCochainUnitApp P) ≫
          (singularSheafCochainFunctor k 0).map (torusCancellationParameterMap k Y) ≫
          singularSheafCochainTorusSectionsMap k C) := by
  intro P C h V a η
  let m := torusCancellationParameterMap k Y
  let K := singularCochainComplex C 0
  let α := singularCochainUnitApp C
  let β := singularCochainUnitApp ((T).obj C)
  let σ := (singularCochainTorusParameterIso k C).hom
  let τ := torusSectionsSheafificationComplexMap k c K
  let e := (HomologicalComplex.singleMapHomologicalComplex (A) c (0 : ℤ)).app C
  let d := (HomologicalComplex.singleMapHomologicalComplex (U) c (0 : ℤ)).app ((A).obj C)
  let j := (HomologicalComplex.singleMapHomologicalComplex (T) c (0 : ℤ)).app C
  let j' := (HomologicalComplex.singleMapHomologicalComplex (T) c (0 : ℤ)).app ((U).obj
    ((A).obj C))
  let u := toNisnevichSheafify k C
  let t := (T).mapHomologicalComplex c
  let W := (R).mapHomologicalComplex c
  have hunit : (sₚ).map u ≫ d.inv = η.app ((sₚ).obj C) ≫ V.map e.hom := by
    have hu := Adjunction.mapHomologicalComplexAdjunction_unit_app_single
      (nisnevichSheafificationAdjunction k) c (0 : ℤ) C
    rw [nisnevichSheafificationAdjunction_unit_app k C] at hu
    exact (Iso.comp_inv_eq d).2 (hu.symm.trans (Category.assoc _ _ _).symm)
  have hd :
      (HomologicalComplex.singleMapHomologicalComplex (R) c (0 : ℤ)).inv.app ((A).obj C) =
        j'.inv ≫ t.map d.inv :=
    HomologicalComplex.singleMapHomologicalComplex_comp_inv_app (U) (T) c (0 : ℤ) ((A).obj C)
  have hn : (sₚ).map ((T).map u) ≫ j'.inv = j.inv ≫ t.map ((sₚ).map u) :=
    (HomologicalComplex.singleMapHomologicalComplex (T) c (0 : ℤ)).inv.naturality u
  have h₀ : (sₚ).map ((T).map u) ≫
      (HomologicalComplex.singleMapHomologicalComplex (R) c (0 : ℤ)).inv.app ((A).obj C) ≫
      W.map h = j.inv ≫ t.map (α ≫ η.app K) := by
    have hV : (sₚ).map u ≫ d.inv ≫ V.map (e.inv ≫ a.map α) = α ≫ η.app K := by
      calc
        _ = (η.app ((sₚ).obj C) ≫ V.map e.hom) ≫ V.map (e.inv ≫ a.map α) :=
          (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hunit)
        _ = η.app ((sₚ).obj C) ≫ V.map (a.map α) := by
          rw [Category.assoc, ← V.map_comp, e.hom_inv_id_assoc]
        _ = _ := (η.naturality α).symm
    have hw : W.map h = t.map (V.map (e.inv ≫ a.map α)) := rfl
    calc
      _ = ((sₚ).map ((T).map u) ≫ j'.inv) ≫
          t.map d.inv ≫ t.map (V.map (e.inv ≫ a.map α)) := by
        rw [hd, hw]
        simp only [Category.assoc]
      _ = j.inv ≫ t.map ((sₚ).map u ≫ d.inv ≫ V.map (e.inv ≫ a.map α)) := by
        rw [hn]
        simp only [Category.assoc, t.map_comp]
      _ = _ := congrArg (j.inv ≫ ·) (t.congr_map hV)
  have hσ : (sₚ).map m ≫ β ≫ σ = (sₚ).map m ≫ j.inv ≫ t.map α := by
    exact congrArg ((sₚ).map m ≫ ·) (singularCochainTorusParameterIso_unit k C)
  let f := singularCochainUnitApp P ≫ (singularCochainFunctor 0).map m ≫ σ
  have hf : f = (sₚ).map m ≫ j.inv ≫ t.map α := by
    have hn' : (sₚ).map m ≫ β = singularCochainUnitApp P ≫
        (singularCochainFunctor 0).map m := singularCochainUnit.naturality m
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ σ) hn'.symm)).trans ((Category.assoc _ _ _).trans hσ)
  calc
    _ = (sₚ).map m ≫ j.inv ≫ t.map (α ≫ η.app K) := by
      rw [torusTensorRepresentableSingleQuotient_homEquiv k Y _ h]
      change (sₚ).map (m ≫ (T).map u) ≫
          (HomologicalComplex.singleMapHomologicalComplex (R) c (0 : ℤ)).inv.app
            ((A).obj C) ≫ W.map h = _
      rw [(sₚ).map_comp, Category.assoc]
      exact congrArg ((sₚ).map m ≫ ·) h₀
    _ = f ≫ t.map (η.app K) := by
      calc
        _ = (sₚ).map m ≫ j.inv ≫ t.map α ≫ t.map (η.app K) :=
          congrArg ((sₚ).map m ≫ j.inv ≫ ·) (t.map_comp α (η.app K))
        _ = ((sₚ).map m ≫ j.inv ≫ t.map α) ≫ t.map (η.app K) := by
          simp only [Category.assoc]
        _ = _ := congrArg (· ≫ t.map (η.app K)) hf.symm
    _ = (f ≫ η.app (t.obj K)) ≫ V.map τ := by
      have hτ : η.app (t.obj K) ≫ V.map τ = t.map (η.app K) :=
        forget_torusSectionsSheafificationComplexMap_unit k K
      exact (congrArg (f ≫ ·) hτ.symm).trans (Category.assoc _ _ _).symm
    _ = η.app ((sₚ).obj P) ≫ V.map (a.map f ≫ τ) := by
      have hη : f ≫ η.app (t.obj K) = η.app ((sₚ).obj P) ≫ V.map (a.map f) :=
        η.naturality f
      exact (congrArg (· ≫ V.map τ) hη).trans
        ((Category.assoc _ _ _).trans
          (congrArg (η.app ((sₚ).obj P) ≫ ·) (V.map_comp _ _).symm))
    _ = _ := by
      rw [singularSheafCochainTorusSectionsMap_eq_placed]
      change η.app ((sₚ).obj P) ≫ V.map (a.map f ≫ τ) =
        η.app ((sₚ).obj P) ≫ V.map (a.map (singularCochainUnitApp P) ≫
          a.map ((singularCochainFunctor 0).map m) ≫ a.map σ ≫ τ)
      simp only [f, a.map_comp, Category.assoc]


end AlgebraicGeometry.SheafWithTransfers
