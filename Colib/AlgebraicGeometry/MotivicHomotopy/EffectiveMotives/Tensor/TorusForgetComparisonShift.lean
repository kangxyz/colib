/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedForgetComparison
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedForgetShift
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.UnitShift
import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.UnboundedLocalization

/-! # Shift of the actual derived torus forget comparison -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers
open Stacks.Injectives.KInjectiveResolution

local notation "c" => ComplexShape.up ℤ

set_option maxHeartbeats 1500000 in
-- The exact derived comparison retains the canonical shift of both composite functors.
private theorem mapDerivedCategorySourceIsoQ_shift
    {A B₀ C : Type*} [Category* A] [Category* B₀] [Category* C]
    [Abelian A] [Abelian B₀] [Abelian C]
    [HasDerivedCategory B₀] [HasDerivedCategory C]
    (F : A ⥤ B₀) (G : B₀ ⥤ C) [F.Additive] [G.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G] :
    NatTrans.CommShift (mapDerivedCategorySourceIsoQ F G).hom ℤ := by
  let L := F.mapHomologicalComplex c
  let E := G.mapDerivedCategory
  let Q := DerivedCategory.Q (C := B₀)
  let Q' := DerivedCategory.Q (C := C)
  let e := G.mapDerivedCategoryFactors
  let M := G.mapHomologicalComplex c
  let t := Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c
  let τ := (Functor.associator L Q E).hom
  let σ := Functor.whiskerLeft L e.hom
  let ω := (Functor.associator L M Q').inv
  let π := Functor.whiskerRight t.hom Q'
  have h : (mapDerivedCategorySourceIsoQ F G).hom = τ ≫ σ ≫ ω ≫ π := by
    ext K
    have ht : t.hom.app K = 𝟙 _ := by ext i; rfl
    have hp : π.app K = 𝟙 _ :=
      (congrArg Q'.map ht).trans (Q'.map_id _)
    change τ.app K ≫ σ.app K = τ.app K ≫ σ.app K ≫ 𝟙 _ ≫ π.app K
    exact congrArg (τ.app K ≫ ·)
      ((Category.comp_id (σ.app K)).symm.trans
        (congrArg (σ.app K ≫ ·) ((Category.id_comp _).trans hp).symm))
  let : NatTrans.CommShift τ ℤ := NatTrans.CommShift.associator Q E ℤ
  let : NatTrans.CommShift e.hom ℤ := inferInstanceAs
    (NatTrans.CommShift G.mapDerivedCategoryFactors.hom ℤ)
  let : NatTrans.CommShift σ ℤ := by
    dsimp only [σ]
    infer_instance
  let : NatTrans.CommShift t.hom ℤ := inferInstanceAs
    (NatTrans.CommShift
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).hom ℤ)
  let : NatTrans.CommShift π ℤ := NatTrans.CommShift.whiskerRight t.hom Q' ℤ
  let : NatTrans.CommShift ω ℤ :=
    NatTrans.CommShift.of_iso_inv (Functor.associator L M Q') ℤ
  let : NatTrans.CommShift (ω ≫ π) ℤ := NatTrans.CommShift.comp ω π ℤ
  let : NatTrans.CommShift (σ ≫ ω ≫ π) ℤ := NatTrans.CommShift.comp σ (ω ≫ π) ℤ
  let : NatTrans.CommShift (τ ≫ σ ≫ ω ≫ π) ℤ :=
    NatTrans.CommShift.comp τ (σ ≫ ω ≫ π) ℤ
  exact NatTrans.commShift_of_eq h

private theorem complexCompositionUnitCommShift
    {A B₀ C : Type*} [Category* A] [Category* B₀] [Category* C]
    [Abelian A] [Abelian B₀] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B₀] [HasDerivedCategory C]
    (F : A ⥤ B₀) (G : B₀ ⥤ C) [F.Additive] [G.Additive]
    {RF : DerivedCategory A ⥤ DerivedCategory B₀}
    {RG : DerivedCategory B₀ ⥤ DerivedCategory C}
    [RF.CommShift ℤ] [RG.CommShift ℤ]
    (α : F.mapHomologicalComplex c ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (β : G.mapHomologicalComplex c ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    [NatTrans.CommShift α ℤ] [NatTrans.CommShift β ℤ] :
    NatTrans.CommShift
      (show (F ⋙ G).mapHomologicalComplex c ⋙ DerivedCategory.Q ⟶
          DerivedCategory.Q ⋙ (RF ⋙ RG) from
        Functor.whiskerLeft (F.mapHomologicalComplex c) β ≫ Functor.whiskerRight α RG) ℤ := by
  let L := F.mapHomologicalComplex c
  let M := G.mapHomologicalComplex c
  let Q₀ := DerivedCategory.Q (C := A)
  let Q₁ := DerivedCategory.Q (C := B₀)
  let Q₂ := DerivedCategory.Q (C := C)
  let t := Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c
  let p := Functor.whiskerRight t.inv Q₂
  let q := (Functor.associator L M Q₂).hom
  let f := Functor.whiskerLeft L β
  let g := (Functor.associator L Q₁ RG).inv
  let b := Functor.whiskerRight α RG
  let d := (Functor.associator Q₀ RF RG).hom
  let ξ : (F ⋙ G).mapHomologicalComplex c ⋙ Q₂ ⟶ Q₀ ⋙ (RF ⋙ RG) := f ≫ b
  have h : ξ = p ≫ q ≫ f ≫ g ≫ b ≫ d := by
    ext K
    have ht : t.inv.app K = 𝟙 _ := by ext i; rfl
    have hp : p.app K = 𝟙 _ :=
      (congrArg Q₂.map ht).trans (Q₂.map_id _)
    let x := β.app (L.obj K)
    let y := RG.map (α.app K)
    change x ≫ y = p.app K ≫ 𝟙 _ ≫ x ≫ 𝟙 _ ≫ y ≫ 𝟙 _
    have hxy : 𝟙 _ ≫ 𝟙 _ ≫ x ≫ 𝟙 _ ≫ y ≫ 𝟙 _ = x ≫ y := by
      calc
        _ = x ≫ 𝟙 _ ≫ y ≫ 𝟙 _ := (Category.id_comp _).trans (Category.id_comp _)
        _ = x ≫ y ≫ 𝟙 _ := congrArg (x ≫ ·) (Category.id_comp _)
        _ = x ≫ y := congrArg (x ≫ ·) (Category.comp_id y)
    exact hxy.symm.trans (congrArg (· ≫ 𝟙 _ ≫ x ≫ 𝟙 _ ≫ y ≫ 𝟙 _) hp.symm)
  let : NatTrans.CommShift t.hom ℤ := inferInstanceAs
    (NatTrans.CommShift
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).hom ℤ)
  let : NatTrans.CommShift t.inv ℤ := NatTrans.CommShift.of_iso_inv t ℤ
  let : NatTrans.CommShift p ℤ := NatTrans.CommShift.whiskerRight t.inv Q₂ ℤ
  let : NatTrans.CommShift q ℤ := NatTrans.CommShift.associator M Q₂ ℤ
  let : NatTrans.CommShift f ℤ := by
    dsimp only [f]
    infer_instance
  let : NatTrans.CommShift g ℤ :=
    NatTrans.CommShift.of_iso_inv (Functor.associator L Q₁ RG) ℤ
  let : NatTrans.CommShift b ℤ := NatTrans.CommShift.whiskerRight α RG ℤ
  let : NatTrans.CommShift d ℤ := NatTrans.CommShift.associator RF RG ℤ
  change NatTrans.CommShift ξ ℤ
  rw [h]
  infer_instance

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "W" => HomologicalComplex.quasiIso NST c
local notation "Qₚ" => DerivedCategory.Q (C := PST)
local notation "Qₛ" => DerivedCategory.Q (C := NST)
local notation "U" => SheafWithTransfers.forget k
local notation "B" => torusSectionsFunctor k
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "T" => (withParameterFunctor Gₘ : PST ⥤ PST)
local notation "R" => forgetDerivedFunctor k
local notation "S" => torusSectionsDerivedFunctor k

/-- The canonical abelian structure on transfer sheaves for the torus forget comparison. -/
local instance instAbelianTorusForgetComparisonShift : Abelian NST := SheafWithTransfers.abelian k

set_option maxHeartbeats 1450000 in
-- Compare the two actual derived units on the original cochain complexes.
/-- The two descriptions of derived torus sections on underlying transfers intertwine shift. -/
theorem torusSectionsDerivedForgetIso_commShift :
    NatTrans.CommShift (torusSectionsDerivedForgetIso k).hom ℤ := by
  let := forgetDerivedUnit_commShift k
  let E := (T).mapDerivedCategory
  let α := torusForgetCompositionUnit k
  let β := torusTensorDerivedRightUnit k
  let t := NatIso.mapHomologicalComplex (torusSectionsUnderlyingIso k).symm c
  let e := Functor.isoWhiskerRight t Qₚ
  let g := (mapDerivedCategorySourceIsoQ (U) (T))
  let b₃ := Functor.whiskerRight (forgetDerivedUnit k) E
  let b₄ := (Functor.associator Qₛ (R) E).hom
  let : NatTrans.CommShift α ℤ :=
    complexCompositionUnitCommShift B U (torusSectionsDerivedUnit k) (forgetDerivedUnit k)
  let : NatTrans.CommShift g.hom ℤ := mapDerivedCategorySourceIsoQ_shift U T
  let : NatTrans.CommShift g.inv ℤ := NatTrans.CommShift.of_iso_inv g ℤ
  let : NatTrans.CommShift b₃ ℤ := NatTrans.CommShift.whiskerRight (forgetDerivedUnit k) E ℤ
  let : NatTrans.CommShift b₄ ℤ := NatTrans.CommShift.associator (F₁ := Qₛ) R E ℤ
  let : NatTrans.CommShift (b₃ ≫ b₄) ℤ := NatTrans.CommShift.comp b₃ b₄ ℤ
  let : NatTrans.CommShift β ℤ := NatTrans.CommShift.comp g.inv (b₃ ≫ b₄) ℤ
  let : NatTrans.CommShift t.hom ℤ := inferInstanceAs
    (NatTrans.CommShift ((torusSectionsUnderlyingIso k).symm.hom.mapHomologicalComplex c) ℤ)
  let : NatTrans.CommShift e.hom ℤ := NatTrans.CommShift.whiskerRight t.hom Qₚ ℤ
  let : (R ⋙ E).IsRightDerivedFunctor β W := by
    apply (isRightDerivedFunctor_iff_isIso_app_of_isKInjective Qₛ _ _
      (invertsQuasiIso_mapHomologicalComplex_comp_Q (U ⋙ T))).2
    intro I hI
    let : IsIso ((forgetDerivedUnit k).app I) :=
      isIso_app_of_isKInjective Qₛ _ _ (invertsQuasiIso_mapHomologicalComplex_comp_Q U) I hI
    change IsIso ((mapDerivedCategorySourceIsoQ (U) (T)).inv.app I ≫
      (E.map ((forgetDerivedUnit k).app I) ≫ (Functor.associator Qₛ _ _).hom.app I))
    infer_instance
  let δ := Functor.rightDerivedNatTrans (S ⋙ R) (R ⋙ E) α β W e.hom
  have h : (torusSectionsDerivedForgetIso k).hom = δ := by
    apply Functor.rightDerived_ext (S ⋙ R) α W
    apply NatTrans.ext
    funext K
    have h₁ : α.app K ≫ (torusSectionsDerivedForgetIso k).hom.app ((Qₛ).obj K) =
        e.hom.app K ≫ β.app K := torusSectionsDerivedForgetIso_hom_app_Q_obj k K
    exact h₁.trans
      (Functor.rightDerivedNatTrans_app (S ⋙ R) (R ⋙ E) α β W e.hom K).symm
  rw [h]
  exact Functor.rightDerivedNatTrans_commShift (S ⋙ R) (R ⋙ E) α β W ℤ e.hom

end AlgebraicGeometry.SheafWithTransfers
