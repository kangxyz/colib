/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.BaseChangedMarkedComponentSections
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenFinalTransportGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootBaseComponentTransportResult
/-! # Actual refinement of the specified descended root and auxiliary pair -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
open Stacks.Divisors Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace AlgebraicGeometry.Scheme.SmoothSite
local instance actualFinalPullbackInvertible {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M hM

/-- Exact nested transport after the actual marked integral-base refinement. -/
def ActualStageRootAuxiliaryRefinement
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {C₀ : Scheme.{u}} (p : C₀ ⟶ X.left)
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    [IsNormal X.left] [IsLocallyNoetherian X.left] [IsNormal C₀]
    [IsProper p] [IsClosedImmersion U.ι] (ℓ : Over i)
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj ℓ.left ⟶
      (etaleStageOpenDiagram X s p i U).obj ℓ)
    [IsClosedImmersion σ] [IsClosedImmersion τ]
    [IsEffectiveCartierDivisor σ.ker] [IsEffectiveCartierDivisor τ.ker]
    (hσ : σ ≫ (etaleStageOpenStructure X s p i U).app ℓ = 𝟙 _)
    (hτ : τ ≫ (etaleStageOpenStructure X s p i U).app ℓ = 𝟙 _)
    (_hmark : etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj ℓ.left) ≫ σ =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj ℓ.left) ≫ τ)
    {Z : Scheme.{u}} (iZ : Z ⟶ (etaleStageOpenDiagram X s p i U).obj ℓ)
    (aD : ∀ z : Z, iZ z ∉ σ.ker.support) (aE : ∀ z : Z, iZ z ∉ τ.ker.support)
    (M N : ((etaleStageOpenDiagram X s p i U).obj ℓ).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      ((etaleStageOpenDiagram X s p i U).obj ℓ).toRingedSpace.presheaf
      (structureSheafRing ((etaleStageOpenDiagram X s p i U).obj ℓ).toRingedSpace).property M]
    (n : ℕ)
    (α : tensorPower ((etaleStageOpenDiagram X s p i U).obj ℓ).toRingedSpace.presheaf
      (structureSheafRing ((etaleStageOpenDiagram X s p i U).obj ℓ).toRingedSpace).property
      M (n : ℤ) ≅ differenceSheaf σ.ker τ.ker)
    (e : (Scheme.Modules.pullback iZ).obj M ≅ SheafOfModules.unit Z.ringCatSheaf)
    (eN : (Scheme.Modules.pullback iZ).obj N ≅ SheafOfModules.unit Z.ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor
      ((etaleStageOpenDiagram X s p i U).obj ℓ).sheaf).obj M).obj N, ⊤))
    (bN : Γ(N, ⊤)) : Prop :=
    ∃ (Anew : EtaleNeighborhood X s.hom)
      (v : Anew ⟶ (smallEtaleNeighborhoodInclusion X s).obj ℓ.left),
    let A₁ := ((etaleNeighborhoodToSmooth X s.hom).obj Anew).left
    let g := ((etaleNeighborhoodToSmooth X s.hom).map v).left
    let q := (etaleStageOpenStructure X s p i U).app ℓ
    let F := pullback.fst q g
    let σ₁ := baseChangedSection q g σ hσ
    let τ₁ := baseChangedSection q g τ hτ
    IsAffine A₁ ∧ IsIntegral A₁ ∧ IsNoetherian A₁ ∧
    ∃ (hG : IsOpenImmersion g) (hGC : IsClosedImmersion g)
      (hCN : IsNormal (pullback q g)) (hCNoeth : IsNoetherian (pullback q g)),
    letI := hG
    letI := hGC
    letI := hCN
    letI := hCNoeth
    let η := etaleNeighborhoodMark X s.hom Anew
    let V := normalComponentOpen (σ₁ (η (IsLocalRing.closedPoint s.residueField)))
    let κ := V.ι
    let i₁ := pullback.fst F iZ
    let b₁ := pullback.snd F iZ
    let i₂ := pullback.fst κ i₁
    let b₂ := pullback.snd κ i₁
    ∃ (σ₂ τ₂ : A₁ ⟶ V.toScheme) (hσ₂ : σ₂ ≫ κ = σ₁) (hτ₂ : τ₂ ≫ κ = τ₁),
    let hs₁ := isPullback_baseChangedSection q g σ hσ
    let ht₁ := isPullback_baseChangedSection q g τ hτ
    letI : IsClosedImmersion σ₁ :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hs₁.flip inferInstance
    letI : IsClosedImmersion τ₁ :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) ht₁.flip inferInstance
    letI : IsEffectiveCartierDivisor σ₁.ker :=
      isEffectiveCartierDivisor_ker_cartesian_of_flat F g σ σ₁ hs₁
    letI : IsEffectiveCartierDivisor τ₁.ker :=
      isEffectiveCartierDivisor_ker_cartesian_of_flat F g τ τ₁ ht₁
    letI : IsEffectiveCartierDivisor σ₂.ker :=
      isEffectiveCartierDivisor_ker_cartesian_of_flat κ (𝟙 A₁) σ₁ σ₂
        (isPullback_section_openRestriction κ σ₁ σ₂ hσ₂)
    letI : IsEffectiveCartierDivisor τ₂.ker :=
      isEffectiveCartierDivisor_ker_cartesian_of_flat κ (𝟙 A₁) τ₁ τ₂
        (isPullback_section_openRestriction κ τ₁ τ₂ hτ₂)
    OriginalRootBaseComponentTransportResult F κ g b₁ b₂ iZ i₁ i₂
      (pullback.condition (f := F) (g := iZ)).symm (pullback.condition (f := κ) (g := i₁)).symm
      σ τ σ₁ τ₁ σ₂ τ₂ hs₁ ht₁ hσ₂ hτ₂ aD aE M n α e N eN a bN

/-- Refine the actual stage and transport only the specified original objects. -/
theorem actualStageRootAuxiliaryRefinement
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {C₀ : Scheme.{u}} (p : C₀ ⟶ X.left)
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    [IsNormal X.left] [IsLocallyNoetherian X.left] [IsNormal C₀]
    [IsProper p] [IsClosedImmersion U.ι] (ℓ : Over i)
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj ℓ.left ⟶
      (etaleStageOpenDiagram X s p i U).obj ℓ)
    [IsClosedImmersion σ] [IsClosedImmersion τ]
    [IsEffectiveCartierDivisor σ.ker] [IsEffectiveCartierDivisor τ.ker]
    (hσ : σ ≫ (etaleStageOpenStructure X s p i U).app ℓ = 𝟙 _)
    (hτ : τ ≫ (etaleStageOpenStructure X s p i U).app ℓ = 𝟙 _)
    (hmark : etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj ℓ.left) ≫ σ =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj ℓ.left) ≫ τ)
    {Z : Scheme.{u}} (iZ : Z ⟶ (etaleStageOpenDiagram X s p i U).obj ℓ)
    (aD : ∀ z : Z, iZ z ∉ σ.ker.support) (aE : ∀ z : Z, iZ z ∉ τ.ker.support)
    (M N : ((etaleStageOpenDiagram X s p i U).obj ℓ).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      ((etaleStageOpenDiagram X s p i U).obj ℓ).toRingedSpace.presheaf
      (structureSheafRing ((etaleStageOpenDiagram X s p i U).obj ℓ).toRingedSpace).property M]
    (n : ℕ)
    (α : tensorPower ((etaleStageOpenDiagram X s p i U).obj ℓ).toRingedSpace.presheaf
      (structureSheafRing ((etaleStageOpenDiagram X s p i U).obj ℓ).toRingedSpace).property
      M (n : ℤ) ≅ differenceSheaf σ.ker τ.ker)
    (e : (Scheme.Modules.pullback iZ).obj M ≅ SheafOfModules.unit Z.ringCatSheaf)
    (eN : (Scheme.Modules.pullback iZ).obj N ≅ SheafOfModules.unit Z.ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor
      ((etaleStageOpenDiagram X s p i U).obj ℓ).sheaf).obj M).obj N, ⊤))
    (bN : Γ(N, ⊤))
    (he : tensorPowerCongr Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property _ _ e n =
      boundaryRootPowerIso iZ M _ n α (differenceSheafBoundaryIso iZ σ.ker τ.ker aD aE))
    (ha : Scheme.Modules.Hom.app (X := Z) (pullbackTensorFrame iZ M N e eN).hom ⊤
      (pullbackGlobalSections iZ _ a) = (1 : Γ(Z, ⊤)))
    (hb : Scheme.Modules.Hom.app (X := Z) eN.hom ⊤ (pullbackGlobalSections iZ N bN) =
      (1 : Γ(Z, ⊤))) :
    ActualStageRootAuxiliaryRefinement X s p i U ℓ σ τ hσ hτ hmark iZ aD aE M N n α e eN a bN := by
  obtain ⟨Anew, v, hAff, hInt, hNoeth, hG, hGC, hF, hFC, hCN, hCNoeth, hPB, hη⟩ :=
    etaleStageOpen_exists_integral_base_refinement X s p i U ℓ
  let := hInt
  let := hG
  let := hGC
  let := hCN
  let := hCNoeth
  let g := ((etaleNeighborhoodToSmooth X s.hom).map v).left
  let q := (etaleStageOpenStructure X s p i U).app ℓ
  let F := pullback.fst q g
  obtain ⟨hsq, htq, hs₁, ht₁, hsk, htk, hsame, σ₂, τ₂, hσ₂, hτ₂,
    hσq, hτq, hs₂, ht₂, hσk, hτk, hσF, hτF, hsame₂⟩ :=
    exists_baseChanged_markedNormalComponent_section_pair q g σ τ hσ hτ
      (etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj ℓ.left))
      (etaleNeighborhoodMark X s.hom Anew) hη hmark
  refine ⟨Anew, v, hAff, hInt, hNoeth, hG, hGC, hCN, hCNoeth, σ₂, τ₂, hσ₂, hτ₂, ?_⟩
  let : IsClosedImmersion (baseChangedSection q g σ hσ) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hs₁.flip inferInstance
  let : IsClosedImmersion (baseChangedSection q g τ hτ) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) ht₁.flip inferInstance
  let : IsEffectiveCartierDivisor (baseChangedSection q g σ hσ).ker :=
    isEffectiveCartierDivisor_ker_cartesian_of_flat F g σ _ hs₁
  let : IsEffectiveCartierDivisor (baseChangedSection q g τ hτ).ker :=
    isEffectiveCartierDivisor_ker_cartesian_of_flat F g τ _ ht₁
  let : IsEffectiveCartierDivisor σ₂.ker :=
    isEffectiveCartierDivisor_ker_cartesian_of_flat _ _ _ σ₂ hs₂
  let : IsEffectiveCartierDivisor τ₂.ker :=
    isEffectiveCartierDivisor_ker_cartesian_of_flat _ _ _ τ₂ ht₂
  exact originalRootBaseComponentTransportResult _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ M n α e he N eN a bN ha hb

end AlgebraicGeometry.Scheme.SmoothSite
