/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenFinalTransportGeometry

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.BaseComponentRestriction
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ActualStageRootAuxiliaryRefinement
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenRefinedBoundarySurjective
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenRetainedAffine

/-! # Restriction at the actual final stage, with the specified root and pair

The integral neighborhood and marked component are constructed, and boundary
surjectivity is deduced from the original finite cover and independent chart.
No second root or auxiliary pair is selected. The actual retained section and
target maps are the input interface; the final equality is not an input.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open Stacks.Divisors Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits
universe u v
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace AlgebraicGeometry.Scheme.SmoothSite

local instance sameRootStageAG (X : Scheme.{u}) (M : X.Modules)
    [h : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ h

local instance sameRootStageUnit (B : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible B.presheaf (ringSheafCond B)
      (SheafOfModules.unit B.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

variable {K : Type u} [Field K]
  (P : PresheafWithTransfers.{v} K) (hP : PresheafWithTransfers.IsA1Invariant P)
  (X : SmoothSite (Spec (.of K))) (s : GeometricPoint X.left)
  {C₀ : Scheme.{u}} (p : C₀ ⟶ X.left)
  [IsNormal X.left] [IsLocallyNoetherian X.left]
  [IsNormal C₀] [IsProper p]
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
  [IsClosedImmersion U.ι] (ℓ : Over i)

local notation "Ai" => etaleStageOpenFixedRing X s i
local notation "Astage" =>
  Functor.obj (smallEtaleNeighborhoodToSmooth X s) (Functor.obj (Over.forget i) ℓ)
local notation "Cstage" => Functor.obj (etaleStageOpenDiagram X s p i U) ℓ
local notation "qstage" => NatTrans.app (etaleStageOpenStructure X s p i U) ℓ

include hP

/-- The same final-stage root and numerator/denominator give the original two
restrictions equal on an actual further marked integral neighborhood. -/
theorem exists_etaleStageOpen_same_root_restriction
    (π : U.toScheme ⟶ projectiveLine Ai) [IsFinite π]
    (hπ : π ≫ (projectiveLine Ai ↘ Spec (.of ↥Ai)) =
      U.ι ≫ (etaleCurveStructure X s p).app i)
    {Y Z E : Scheme.{u}} [IsAffine Y]
    (j : Y ⟶ U.toScheme) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ U.ι ≫ (etaleCurveStructure X s p).app i)]
    (cY : Y ⟶ Spec (.of (Polynomial Ai)))
    (hcY : cY ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : Ai →+* Polynomial Ai)) =
      j ≫ (U.ι ≫ (etaleCurveStructure X s p).app i))
    (hj : j ≫ π = cY ≫ projectiveLineXChart Ai)
    {N₀ : Scheme.{u}} [IrreducibleSpace N₀]
    (r₀ : U.toScheme ⟶ N₀) [Flat r₀]
    (eChart : E ⟶ N₀) [IsOpenImmersion eChart] [Nonempty E]
    (cE : Limits.pullback r₀ eChart ⟶ Spec (.of (Polynomial Ai))) [Etale cE]
    (hcE : cE ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : Ai →+* Polynomial Ai)) =
      Limits.pullback.fst r₀ eChart ≫ (U.ι ≫ (etaleCurveStructure X s p).app i))
    (heChart : Limits.pullback.fst r₀ eChart ≫ π = cE ≫ projectiveLineXChart Ai)
    (d : Z ⟶ U.toScheme) (hd : Set.range d = (Set.range j)ᶜ)
    (σ τ : (Astage).left ⟶ Cstage)
    [_hSigmaClosed : IsClosedImmersion σ] [_hTauClosed : IsClosedImmersion τ]
    [_hSigmaCartier : IsEffectiveCartierDivisor σ.ker]
    [_hTauCartier : IsEffectiveCartierDivisor τ.ker]
    (hσ : σ ≫ qstage = 𝟙 _) (hτ : τ ≫ qstage = 𝟙 _)
    (hmark : etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj ℓ.left) ≫ σ =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj ℓ.left) ≫ τ)
    (σY τY : (Astage).left ⟶ (etaleStageOpenBoundaryDiagram X s p i U j).obj ℓ)
    (hσY : σY ≫ (etaleStageOpenBoundaryMap X s p i U j).app ℓ = σ)
    (hτY : τY ≫ (etaleStageOpenBoundaryMap X s p i U j).app ℓ = τ)
    {T : SmoothSite (Spec (.of K))}
    (r : (etaleStageOpenBoundaryDiagram X s p i U j).obj ℓ ⟶
      Limits.pullback (Astage).hom T.hom)
    (hr : r ≫ Limits.pullback.fst (Astage).hom T.hom =
      (etaleStageOpenBoundaryMap X s p i U j).app ℓ ≫ qstage)
    (f g : Astage ⟶ T)
    (hf : f.left = σY ≫ r ≫ Limits.pullback.snd (Astage).hom T.hom)
    (hg : g.left = τY ≫ r ≫ Limits.pullback.snd (Astage).hom T.hom)
    (aD : ∀ z : (etaleStageOpenBoundaryDiagram X s p i U d).obj ℓ,
      (etaleStageOpenBoundaryMap X s p i U d).app ℓ z ∉ σ.ker.support)
    (aE : ∀ z : (etaleStageOpenBoundaryDiagram X s p i U d).obj ℓ,
      (etaleStageOpenBoundaryMap X s p i U d).app ℓ z ∉ τ.ker.support)
    (M N : (Cstage).Modules)
    [hM : Stacks.SheafOfModules.IsInvertible (Cstage).presheaf (Cstage).ringCatIsSheaf M]
    [_hN : Stacks.SheafOfModules.IsInvertible (Cstage).presheaf (Cstage).ringCatIsSheaf N]
    (k : ℕ)
    (hn : ∀ (A : SmoothSite (Spec (.of K)))
      (z : PresheafWithTransfers.sections P ((Cor.graphFunctor K).obj A)), (k + 1) • z = 0)
    (α : Stacks.SheafOfModules.schemeTensorPower Cstage M hM ((k + 1 : ℕ) : ℤ) ≅
      differenceSheaf σ.ker τ.ker)
    (e : (Scheme.Modules.pullback ((etaleStageOpenBoundaryMap X s p i U d).app ℓ)).obj M ≅
      SheafOfModules.unit ((etaleStageOpenBoundaryDiagram X s p i U d).obj ℓ).ringCatSheaf)
    (eN : (Scheme.Modules.pullback ((etaleStageOpenBoundaryMap X s p i U d).app ℓ)).obj N ≅
      SheafOfModules.unit ((etaleStageOpenBoundaryDiagram X s p i U d).obj ℓ).ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor (Cstage).sheaf).obj M).obj N, ⊤))
    (bN : Γ(N, ⊤))
    (he : tensorPowerCongr
      ((etaleStageOpenBoundaryDiagram X s p i U d).obj ℓ).presheaf
      (ringSheafCond ((etaleStageOpenBoundaryDiagram X s p i U d).obj ℓ)) _ _ e (k + 1) =
      boundaryRootPowerIso ((etaleStageOpenBoundaryMap X s p i U d).app ℓ) M _ (k + 1) α
        (differenceSheafBoundaryIso ((etaleStageOpenBoundaryMap X s p i U d).app ℓ)
          σ.ker τ.ker aD aE))
    (ha : Scheme.Modules.Hom.app (X := (etaleStageOpenBoundaryDiagram X s p i U d).obj ℓ)
      (M := (Scheme.Modules.pullback ((etaleStageOpenBoundaryMap X s p i U d).app ℓ)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (Cstage).sheaf).obj M).obj N))
      (N := SheafOfModules.unit
        ((etaleStageOpenBoundaryDiagram X s p i U d).obj ℓ).ringCatSheaf)
      (pullbackTensorFrame ((etaleStageOpenBoundaryMap X s p i U d).app ℓ)
      M N e eN).hom ⊤
      (pullbackGlobalSections ((etaleStageOpenBoundaryMap X s p i U d).app ℓ) _ a) =
        (1 : Γ((etaleStageOpenBoundaryDiagram X s p i U d).obj ℓ, ⊤)))
    (hb : Scheme.Modules.Hom.app (X := (etaleStageOpenBoundaryDiagram X s p i U d).obj ℓ)
      (M := (Scheme.Modules.pullback ((etaleStageOpenBoundaryMap X s p i U d).app ℓ)).obj N)
      (N := SheafOfModules.unit
        ((etaleStageOpenBoundaryDiagram X s p i U d).obj ℓ).ringCatSheaf) eN.hom ⊤
      (pullbackGlobalSections ((etaleStageOpenBoundaryMap X s p i U d).app ℓ) N bN) =
        (1 : Γ((etaleStageOpenBoundaryDiagram X s p i U d).obj ℓ, ⊤))) :
    ∃ (Anew : EtaleNeighborhood X s.hom)
      (v : Anew ⟶ (smallEtaleNeighborhoodInclusion X s).obj ℓ.left),
      let A₁ := ((etaleNeighborhoodToSmooth X s.hom).obj Anew).left
      let v₁ := ((etaleNeighborhoodToSmooth X s.hom).map v).left
      IsAffine A₁ ∧ IsIntegral A₁ ∧ IsNoetherian A₁ ∧
      ∃ (hv : IsOpenImmersion v₁) (hvC : IsClosedImmersion v₁)
        (hCN : IsNormal (Limits.pullback qstage v₁))
        (hCNoeth : IsNoetherian (Limits.pullback qstage v₁)),
      let := hv
      let := hvC
      let := hCN
      let := hCNoeth
      let σ₁ := baseChangedSection qstage v₁ σ hσ
      let τ₁ := baseChangedSection qstage v₁ τ hτ
      let x := σ₁ ((etaleNeighborhoodMark X s.hom Anew) (IsLocalRing.closedPoint s.residueField))
      ∃ (σ₂ τ₂ : A₁ ⟶ (normalComponentOpen x).toScheme),
        σ₂ ≫ (normalComponentOpen x).ι = σ₁ ∧
        τ₂ ≫ (normalComponentOpen x).ι = τ₁ ∧
        ((PresheafWithTransfers.toPresheaf K).obj P).map
            (((etaleNeighborhoodToSmooth X s.hom).map v) ≫ f).op =
          ((PresheafWithTransfers.toPresheaf K).obj P).map
            (((etaleNeighborhoodToSmooth X s.hom).map v) ≫ g).op := by
  let _hStageProper : IsProper qstage :=
    etaleStageOpenStructure_isProper X s p i U ℓ
  obtain ⟨Anew, v, hAff, hInt, hNoeth, hG, hGC, hF, hFC, hCN, hCNoeth, hPB, hη⟩ :=
    etaleStageOpen_exists_integral_base_refinement X s p i U ℓ
  let := hAff
  let := hInt
  let := hNoeth
  let := hG
  let := hGC
  let := hCN
  let := hCNoeth
  let v₁ := ((etaleNeighborhoodToSmooth X s.hom).map v).left
  obtain ⟨hsq, htq, hs₁, ht₁, hsk, htk, hsame, σ₂, τ₂, hσ₂, hτ₂,
    hσq, hτq, hs₂, ht₂, hσk, hτk, hσF, hτF, hsame₂⟩ :=
    exists_baseChanged_markedNormalComponent_section_pair qstage v₁ σ τ hσ hτ
      (etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj ℓ.left))
      (etaleNeighborhoodMark X s.hom Anew) hη hmark
  let x := (baseChangedSection qstage v₁ σ hσ)
    ((etaleNeighborhoodMark X s.hom Anew) (IsLocalRing.closedPoint s.residueField))
  let hsurj := etaleStageOpen_refined_component_boundary_surjective
    X s p i U ℓ Anew v π hπ j cY hcY hj r₀ eChart cE hcE heChart d hd x
  let hYA := etaleStageOpenRetained_stage_isAffine X s p i U j ℓ
  have hdStage := etaleStageOpenRetained_stage_complement X s p i U j d hd ℓ
  refine ⟨Anew, v, hAff, hInt, hNoeth, hG, hGC, hCN, hCNoeth,
    σ₂, τ₂, hσ₂, hτ₂, ?_⟩
  exact PresheafWithTransfers.restriction_baseComponent_same_root
    (_hProper := _hStageProper) (_hAffBase := hAff) (_hIntegralBase := hInt)
    (_hBaseOpen := hG) (_hBaseClosed := hGC)
    (_hCurveNormal := hCN) (_hCurveNoetherian := hCNoeth)
    (_hRetainedAffine := hYA) (_hBoundarySurjective := hsurj)
    (_hRetainedOpen := etaleStageOpenRetained_stage_isOpenImmersion X s p i U j ℓ)
    (_hRetainedSmooth := etaleStageOpenRetained_stage_smooth X s p i U j ℓ)
    (_hSigmaClosed := _hSigmaClosed) (_hTauClosed := _hTauClosed)
    (_hSigmaCartier := _hSigmaCartier) (_hTauCartier := _hTauCartier)
    (hM := hM) (_hN := _hN) P hP
    ((etaleNeighborhoodToSmooth X s.hom).map v) qstage
    ((etaleStageOpenBoundaryMap X s p i U j).app ℓ)
    ((etaleStageOpenBoundaryMap X s p i U d).app ℓ) hdStage
    σ τ hσ hτ σY τY hσY hτY x σ₂ τ₂ hσ₂ hτ₂
    r hr f g hf hg aD aE M N k (hn _) α e eN a bN he ha hb

end AlgebraicGeometry.Scheme.SmoothSite
