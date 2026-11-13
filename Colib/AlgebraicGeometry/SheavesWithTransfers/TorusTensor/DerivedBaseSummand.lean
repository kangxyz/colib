/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.Reduced
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.UnitSplit
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedForgetComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryNatTrans

/-!
# The base summand under derived forget and reindexing

The derived forget comparison carries the literal unit restriction
and constant section of the derived torus to those of the exact
presheaf reindexing. The maps are compared on the original K-injective
models through the actual comparison units.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u w₁ w₂ w₃

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers Stacks.DerivedFunctor Stacks.Injectives.KInjectiveResolution

variable (k : Type u) [Field k]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "S" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject S
local notation "c" => ComplexShape.up ℤ
local notation "U" => (SheafWithTransfers.forget k : NST ⥤ PST)
local notation "B" => (torusSectionsFunctor k : NST ⥤ NST)
local notation "T" => (withParameterFunctor Gₘ : PST ⥤ PST)

/-- Presheaf restriction to the original unit in ordinary base coordinates. -/
def torusPresheafUnitNatTrans : T ⟶ 𝟭 PST :=
  torusParameterRestriction k ≫ (baseSectionsPresheafNatIso k).inv

/-- Original constant sections on a presheaf in ordinary base coordinates. -/
def torusPresheafConstantNatTrans : 𝟭 PST ⟶ T :=
  (baseSectionsPresheafNatIso k).hom ≫ torusParameterConstant k

private theorem torusPresheafUnitNatTrans_app_forget (F : NST) :
    (torusPresheafUnitNatTrans k).app ((U).obj F) = (U).map ((torusSectionsUnitNatTrans k).app F) :=
  rfl

private theorem torusPresheafConstantNatTrans_app_forget (F : NST) :
    (torusPresheafConstantNatTrans k).app ((U).obj F) =
      (U).map ((torusSectionsConstantNatTrans k).app F) :=
  rfl

/-- Restriction to the torus unit on the original presheaf complexes. -/
def presheafComplexRestriction :
    (T).mapHomologicalComplex c ⟶ 𝟭 (CochainComplex PST ℤ) :=
  (torusPresheafUnitNatTrans k).mapHomologicalComplex c ≫
    (Functor.mapHomologicalComplexIdIso _ c).hom

/-- Constant torus sections on the original presheaf complexes. -/
def presheafComplexConstant :
    𝟭 (CochainComplex PST ℤ) ⟶ (T).mapHomologicalComplex c :=
  (Functor.mapHomologicalComplexIdIso _ c).inv ≫
    (torusPresheafConstantNatTrans k).mapHomologicalComplex c

private abbrev sheafComplexConstant :
    𝟭 (CochainComplex NST ℤ) ⟶ (B).mapHomologicalComplex c :=
  (Functor.mapHomologicalComplexIdIso _ c).inv ≫
    (torusSectionsConstantNatTrans k).mapHomologicalComplex c

private theorem presheafComplexRestriction_app_forget (K : CochainComplex NST ℤ) :
    (presheafComplexRestriction k).app (((U).mapHomologicalComplex c).obj K) =
      ((U).mapHomologicalComplex c).map ((torusSectionsComplexUnitRestriction k).app K) := by
  apply HomologicalComplex.hom_ext
  intro i
  exact torusPresheafUnitNatTrans_app_forget k (K.X i)

private theorem presheafComplexConstant_app_forget (K : CochainComplex NST ℤ) :
    (presheafComplexConstant k).app (((U).mapHomologicalComplex c).obj K) =
      ((U).mapHomologicalComplex c).map ((sheafComplexConstant k).app K) := by
  apply HomologicalComplex.hom_ext
  intro i
  exact torusPresheafConstantNatTrans_app_forget k (K.X i)

variable [HasDerivedCategory.{w₁} (PresheafWithTransfers.{u + 1} k)]
variable [HasDerivedCategory.{w₂} (SheafWithTransfers.{u + 1} k)]

set_option quotPrecheck false in
local notation "Qₛ" => DerivedCategory.Q (C := NST)
set_option quotPrecheck false in
local notation "Qₚ" => DerivedCategory.Q (C := PST)
local notation "R" => forgetDerivedFunctor k
set_option quotPrecheck false in
local notation "D" => (T).mapDerivedCategory

/-- The original restriction map on the exact derived presheaf reindexing. -/
def torusPresheafDerivedUnitRestriction : D ⟶ 𝟭 (DerivedCategory PST) :=
  mapDerivedNatTrans (torusPresheafUnitNatTrans k) ≫ (Functor.mapDerivedCategoryIdIso PST).hom

/-- The original constant section on the exact derived presheaf reindexing. -/
def torusPresheafDerivedConstant : 𝟭 (DerivedCategory PST) ⟶ D :=
  (Functor.mapDerivedCategoryIdIso PST).inv ≫ mapDerivedNatTrans (torusPresheafConstantNatTrans k)

omit [HasDerivedCategory NST] in
/-- Restriction on the derived category is induced by the original cochain restriction. -/
theorem torusPresheafDerivedUnitRestriction_app_Q_obj (J : CochainComplex PST ℤ) :
    (T).mapDerivedCategoryFactors.inv.app J ≫
      (torusPresheafDerivedUnitRestriction k).app ((Qₚ).obj J) =
    (Qₚ).map ((presheafComplexRestriction k).app J) := by
  let e := (T).mapDerivedCategoryFactors.app J
  let d := (𝟭 PST).mapDerivedCategoryFactors.app J
  let f := (Functor.mapHomologicalComplexIdIso PST c).hom.app J
  let a := mapDerivedNatTrans (torusPresheafUnitNatTrans k)
  let q := (Qₚ).map (((torusPresheafUnitNatTrans k).mapHomologicalComplex c).app J)
  have h : a.app ((Qₚ).obj J) ≫ d.hom = e.hom ≫ q :=
    mapDerivedNatTrans_factors_app (torusPresheafUnitNatTrans k) J
  have hd : (Functor.mapDerivedCategoryIdIso PST).hom.app ((Qₚ).obj J) =
      d.hom ≫ (Qₚ).map f := Functor.mapDerivedCategoryIdIso_hom_app J
  change e.inv ≫ (a.app ((Qₚ).obj J) ≫
    (Functor.mapDerivedCategoryIdIso PST).hom.app ((Qₚ).obj J)) = _
  calc
    _ = e.inv ≫ (a.app ((Qₚ).obj J) ≫ d.hom) ≫ (Qₚ).map f := by
      rw [hd]
      exact congrArg (e.inv ≫ ·) (Category.assoc _ _ _).symm
    _ = e.inv ≫ (e.hom ≫ q) ≫ (Qₚ).map f :=
      congrArg (fun m => e.inv ≫ m ≫ (Qₚ).map f) h
    _ = _ := by
      simp only [Category.assoc, e.inv_hom_id_assoc]
      exact ((Qₚ).map_comp _ _).symm

omit [HasDerivedCategory NST] in
/-- The derived constant section is induced by the original cochain map. -/
theorem torusPresheafDerivedConstant_app_Q_obj (J : CochainComplex PST ℤ) :
    (torusPresheafDerivedConstant k).app ((Qₚ).obj J) =
      (Qₚ).map ((presheafComplexConstant k).app J) ≫ (T).mapDerivedCategoryFactors.inv.app J := by
  let e := (T).mapDerivedCategoryFactors.app J
  let d := (𝟭 PST).mapDerivedCategoryFactors.app J
  let f := (Functor.mapHomologicalComplexIdIso PST c).inv.app J
  let a := mapDerivedNatTrans (torusPresheafConstantNatTrans k)
  let q := (Qₚ).map (((torusPresheafConstantNatTrans k).mapHomologicalComplex c).app J)
  have h : a.app ((Qₚ).obj J) ≫ e.hom = d.hom ≫ q :=
    mapDerivedNatTrans_factors_app (torusPresheafConstantNatTrans k) J
  have hd : (Functor.mapDerivedCategoryIdIso PST).inv.app ((Qₚ).obj J) =
      (Qₚ).map f ≫ d.inv := by
    let z := (Functor.mapDerivedCategoryIdIso PST).app ((Qₚ).obj J)
    let i := (Functor.mapHomologicalComplexIdIso PST c).app J
    have hz : z.hom = d.hom ≫ (Qₚ).map i.hom :=
      Functor.mapDerivedCategoryIdIso_hom_app J
    change z.inv = (Qₚ).map i.inv ≫ d.inv
    exact (Iso.inv_eq_inv z (d ≪≫ (Qₚ).mapIso i)).2 hz
  have ha : d.inv ≫ a.app ((Qₚ).obj J) = q ≫ e.inv := by
    apply (cancel_mono e.hom).1
    calc
      _ = d.inv ≫ (d.hom ≫ q) := (Category.assoc _ _ _).trans (congrArg (d.inv ≫ ·) h)
      _ = q := d.inv_hom_id_assoc q
      _ = _ := ((Category.assoc q e.inv e.hom).trans
        ((congrArg (q ≫ ·) e.inv_hom_id).trans (Category.comp_id q))).symm
  change (Functor.mapDerivedCategoryIdIso PST).inv.app ((Qₚ).obj J) ≫
    a.app ((Qₚ).obj J) = _
  rw [hd, Category.assoc, ha, ← Category.assoc, ← (Qₚ).map_comp]
  rfl

variable [HasDerivedCategory.{w₃} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

@[reassoc]
private theorem torusSectionsDerivedForgetIso_app_compatibility
    (K : CochainComplex NST ℤ) :
    (torusForgetCompositionUnit k).app K ≫
        (torusSectionsDerivedForgetIso k).hom.app ((Qₛ).obj K) =
      (T).mapDerivedCategoryFactors.inv.app (((U).mapHomologicalComplex c).obj K) ≫
        (D).map ((forgetDerivedUnit k).app K) := by
  rw [torusSectionsDerivedForgetIso_hom_app_Q_obj, torusTensorDerivedRightUnit_app]
  let f := (NatIso.mapHomologicalComplex (torusSectionsUnderlyingIso k).symm c).hom.app K
  have h : (Qₚ).map f = 𝟙 _ := (Qₚ).map_id _
  exact (congrArg (· ≫ _) h).trans (Category.id_comp _)

omit [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})] in
private theorem forgetUnitRestriction_on_complex (K : CochainComplex NST ℤ) :
    (torusForgetCompositionUnit k).app K ≫
        (R).map ((torusSectionsDerivedUnitRestriction k).app ((Qₛ).obj K)) =
      (Qₚ).map ((presheafComplexRestriction k).app (((U).mapHomologicalComplex c).obj K)) ≫
        (forgetDerivedUnit k).app K := by
  let f := (torusSectionsComplexUnitRestriction k).app K
  let r := (torusSectionsDerivedUnitRestriction k).app ((Qₛ).obj K)
  let a := (forgetDerivedUnit k).app (((B).mapHomologicalComplex c).obj K)
  let b := (torusSectionsDerivedUnit k).app K
  let V := (U).mapHomologicalComplex c
  have h : b ≫ r = (Qₛ).map f := torusSectionsDerivedUnitRestriction_app_Q_obj k K
  have hn : (Qₚ).map (V.map f) ≫ (forgetDerivedUnit k).app K = a ≫ (R).map ((Qₛ).map f) :=
    (forgetDerivedUnit k).naturality f
  rw [torusForgetCompositionUnit_app, presheafComplexRestriction_app_forget]
  change (a ≫ (R).map b) ≫ (R).map r = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (a ≫ ·) (((R).map_comp b r).symm.trans ((R).congr_map h))).trans hn.symm)

/-- Derived forget carries restriction to the actual torus unit to the
original exact presheaf restriction. -/
@[reassoc]
theorem torusSectionsDerivedForgetIso_hom_app_unitRestriction (K : DerivedCategory NST) :
    (torusSectionsDerivedForgetIso k).hom.app K ≫
      (torusPresheafDerivedUnitRestriction k).app ((R).obj K) =
    (R).map ((torusSectionsDerivedUnitRestriction k).app K) := by
  let X := (Qₛ).objPreimage K
  obtain ⟨I, f, hI, hf⟩ := Stacks.Injectives.exists_kInjective_resolution_of_grothendieck X
  let : QuasiIso f := hf
  let e : (Qₛ).obj I ≅ K := (asIso ((Qₛ).map f)).symm ≪≫ (Qₛ).objObjPreimageIso K
  let α := (torusSectionsDerivedForgetIso k).hom
  let ρ := torusPresheafDerivedUnitRestriction k
  let σ := torusSectionsDerivedUnitRestriction k
  have h₀ : α.app ((Qₛ).obj I) ≫ ρ.app ((R).obj ((Qₛ).obj I)) =
      (R).map (σ.app ((Qₛ).obj I)) := by
    let : IsIso ((torusForgetCompositionUnit k).app I) :=
      isIso_app_of_isKInjective Qₛ _ _ (invertsQuasiIso_mapHomologicalComplex_comp_Q (B ⋙ U)) I hI
    apply (cancel_epi ((torusForgetCompositionUnit k).app I)).1
    let J := ((U).mapHomologicalComplex c).obj I
    let a := (forgetDerivedUnit k).app I
    let d := (T).mapDerivedCategoryFactors.inv.app J
    have hα : (torusForgetCompositionUnit k).app I ≫ α.app ((Qₛ).obj I) = d ≫ (D).map a :=
      torusSectionsDerivedForgetIso_app_compatibility k I
    have hρ : (D).map a ≫ ρ.app ((R).obj ((Qₛ).obj I)) = ρ.app ((Qₚ).obj J) ≫ a :=
      ρ.naturality a
    calc
      _ = (d ≫ (D).map a) ≫ ρ.app ((R).obj ((Qₛ).obj I)) :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hα)
      _ = d ≫ ρ.app ((Qₚ).obj J) ≫ a :=
        (Category.assoc _ _ _).trans (congrArg (d ≫ ·) hρ)
      _ = (Qₚ).map ((presheafComplexRestriction k).app J) ≫ a :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ a) (torusPresheafDerivedUnitRestriction_app_Q_obj k J))
      _ = _ := (forgetUnitRestriction_on_complex k I).symm
  let B' := torusSectionsDerivedFunctor k
  let K₀ := (Qₛ).obj I
  let i := (B' ⋙ (R)).mapIso e
  let f : (R).obj K₀ ⟶ (R).obj K := (R).map e.hom
  let g := i.hom
  have hα : g ≫ α.app K = α.app K₀ ≫ (D).map f := α.naturality e.hom
  have hρ : (D).map f ≫ ρ.app ((R).obj K) = ρ.app ((R).obj K₀) ≫ f :=
    ρ.naturality f
  have hσ : g ≫ (R).map (σ.app K) = (R).map (σ.app K₀) ≫ f := by
    exact ((R).map_comp _ _).symm.trans
      (((R).congr_map (σ.naturality e.hom)).trans ((R).map_comp _ _))
  let transport : (((R).obj (B'.obj K)) ⟶ (R).obj K) ≃
      (((R).obj (B'.obj K₀)) ⟶ (R).obj K) := i.symm.homFromEquiv
  change α.app K ≫ ρ.app ((R).obj K) = (R).map (σ.app K)
  apply transport.injective
  change g ≫ (α.app K ≫ ρ.app ((R).obj K)) = g ≫ (R).map (σ.app K)
  calc
    _ = (α.app K₀ ≫ (D).map f) ≫ ρ.app ((R).obj K) :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hα)
    _ = (α.app K₀ ≫ ρ.app ((R).obj K₀)) ≫ f :=
      (Category.assoc _ _ _).trans
        ((congrArg (α.app K₀ ≫ ·) hρ).trans (Category.assoc _ _ _).symm)
    _ = _ := (congrArg (· ≫ f) h₀).trans hσ.symm

/-- Derived forget carries the actual constant section to the constant
section of the exact presheaf reindexing. -/
@[reassoc]
theorem torusSectionsDerivedForgetIso_hom_app_constant (K : DerivedCategory NST) :
    (R).map ((torusSectionsDerivedConstant k).app K) ≫
      (torusSectionsDerivedForgetIso k).hom.app K =
    (torusPresheafDerivedConstant k).app ((R).obj K) := by
  let X := (Qₛ).objPreimage K
  obtain ⟨I, f, hI, hf⟩ := Stacks.Injectives.exists_kInjective_resolution_of_grothendieck X
  let : QuasiIso f := hf
  let e : (Qₛ).obj I ≅ K := (asIso ((Qₛ).map f)).symm ≪≫ (Qₛ).objObjPreimageIso K
  let α := (torusSectionsDerivedForgetIso k).hom
  let τ := torusPresheafDerivedConstant k
  let σ := torusSectionsDerivedConstant k
  have h₀ : (R).map (σ.app ((Qₛ).obj I)) ≫ α.app ((Qₛ).obj I) =
      τ.app ((R).obj ((Qₛ).obj I)) := by
    let : IsIso ((forgetDerivedUnit k).app I) :=
      isIso_app_of_isKInjective Qₛ _ _ (invertsQuasiIso_mapHomologicalComplex_comp_Q U) I hI
    apply (cancel_epi ((forgetDerivedUnit k).app I)).1
    let J := ((U).mapHomologicalComplex c).obj I
    let a := (forgetDerivedUnit k).app I
    let a' := (forgetDerivedUnit k).app (((B).mapHomologicalComplex c).obj I)
    let b := (torusSectionsDerivedUnit k).app I
    let f := (sheafComplexConstant k).app I
    let x := ((U).mapHomologicalComplex c).map f
    let z := (T).mapDerivedCategoryFactors.inv.app J
    have hσ : σ.app ((Qₛ).obj I) = (Qₛ).map f ≫ b :=
      torusSectionsDerivedConstant_app_Q_obj k I
    have hn : a ≫ (R).map ((Qₛ).map f) = (Qₚ).map x ≫ a' :=
      ((forgetDerivedUnit k).naturality f).symm
    have hα : (a' ≫ (R).map b) ≫ α.app ((Qₛ).obj I) = z ≫ (D).map a :=
      (congrArg (· ≫ α.app ((Qₛ).obj I)) (torusForgetCompositionUnit_app k I).symm).trans
        (torusSectionsDerivedForgetIso_app_compatibility k I)
    have hτ : τ.app ((Qₚ).obj J) = (Qₚ).map x ≫ z :=
      (torusPresheafDerivedConstant_app_Q_obj k J).trans
        (congrArg (fun m => (Qₚ).map m ≫ z) (presheafComplexConstant_app_forget k I))
    change a ≫ ((R).map (σ.app ((Qₛ).obj I)) ≫ α.app ((Qₛ).obj I)) = _
    calc
      _ = (a ≫ (R).map ((Qₛ).map f)) ≫ (R).map b ≫ α.app ((Qₛ).obj I) := by
        rw [hσ, (R).map_comp]
        simp only [Category.assoc]
      _ = (Qₚ).map x ≫ (a' ≫ (R).map b) ≫ α.app ((Qₛ).obj I) := by
        rw [hn]
        simp only [Category.assoc]
      _ = ((Qₚ).map x ≫ z) ≫ (D).map a :=
        (congrArg ((Qₚ).map x ≫ ·) hα).trans (Category.assoc _ _ _).symm
      _ = a ≫ τ.app ((R).obj ((Qₛ).obj I)) :=
        (congrArg (· ≫ (D).map a) hτ.symm).trans (τ.naturality a).symm
  let B' := torusSectionsDerivedFunctor k
  let K₀ := (Qₛ).obj I
  let i := (R).mapIso e
  let f := i.hom
  let g : (R).obj (B'.obj K₀) ⟶ (R).obj (B'.obj K) := (R).map (B'.map e.hom)
  have hα : g ≫ α.app K = α.app K₀ ≫ (D).map f := α.naturality e.hom
  have hτ : f ≫ τ.app ((R).obj K) = τ.app ((R).obj K₀) ≫ (D).map f := τ.naturality f
  have hσ : f ≫ (R).map (σ.app K) = (R).map (σ.app K₀) ≫ g := by
    exact ((R).map_comp _ _).symm.trans
      (((R).congr_map (σ.naturality e.hom)).trans ((R).map_comp _ _))
  let transport : ((R).obj K ⟶ (D).obj ((R).obj K)) ≃
      ((R).obj K₀ ⟶ (D).obj ((R).obj K)) := i.symm.homFromEquiv
  change (R).map (σ.app K) ≫ α.app K = τ.app ((R).obj K)
  apply transport.injective
  change f ≫ ((R).map (σ.app K) ≫ α.app K) = f ≫ τ.app ((R).obj K)
  calc
    _ = ((R).map (σ.app K₀) ≫ g) ≫ α.app K :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hσ)
    _ = ((R).map (σ.app K₀) ≫ α.app K₀) ≫ (D).map f :=
      (Category.assoc _ _ _).trans
        ((congrArg ((R).map (σ.app K₀) ≫ ·) hα).trans (Category.assoc _ _ _).symm)
    _ = _ := (congrArg (· ≫ (D).map f) h₀).trans hτ.symm

end AlgebraicGeometry.SheafWithTransfers
