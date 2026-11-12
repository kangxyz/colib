/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenSectionDivisors
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenBoundaryNoetherian
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootAuxiliaryFramesConsumerInvertiblePair
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.EtaleStageOpenSameRootRestriction
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ActualStageRootAuxiliaryRefinement
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenAllMarkings
public import Colib.AlgebraicGeometry.Divisors.DifferenceSheafPicard

/-! # Same-witness descent continuation into actual-stage restriction

The original Result is an input, not recomputed. Its complete recovery equations
are retained in WithFinal, whose terminal property records the actual further
neighborhood equality. The auxiliary invertibility comes from its original Nj.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules Stacks.Divisors
open Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits
universe u v
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace AlgebraicGeometry.Scheme.SmoothSite

local instance actualRefinedResultPullbackInvertible
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [_hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M _hM

/-- The original Result, with an actual same-witness refinement inside its final leaf. -/
def EtaleStageOpenRestrictionConsumerResult
    {K : Type u} [Field K] (P : PresheafWithTransfers.{v} K)
    (hP : PresheafWithTransfers.IsA1Invariant P)
    (X : SmoothSite (Spec (.of K)))
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    {Z : Scheme.{u}} (d : Z ⟶ U.toScheme)
    [IsLocallyNoetherian X.left] [IsProper p] [IsClosedImmersion U.ι]
    [IsClosedImmersion d]
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme (Spec (.of K))).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hτ : τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    [IsClosedImmersion σ] [IsClosedImmersion τ]
    [IsSeparated (U.ι ≫ (etaleCurveStructure X s p).app i)]
    {V : Scheme.{u}} [IsAffine V] (j : V ⟶ U.toScheme) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ (U.ι ≫ (etaleCurveStructure X s p).app i))]
    (hσj : Set.range σ ⊆ Set.range j) (hτj : Set.range τ ⊆ Set.range j)
    (hdσ : ∀ z : Z, d z ∉ Set.range σ) (hdτ : ∀ z : Z, d z ∉ Set.range τ)
    (a₀ : Over i)
    [IsNormal X.left] [IsNormal N]
    (hmark : etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a₀.left) ≫
          etaleStageOpenSection X s p i U σ hσ a₀ =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a₀.left) ≫
          etaleStageOpenSection X s p i U τ hτ a₀)
    (π : U.toScheme ⟶ projectiveLine (etaleStageOpenFixedRing X s i)) [IsFinite π]
    (hπ : π ≫ (projectiveLine (etaleStageOpenFixedRing X s i) ↘
        Spec (.of ↥(etaleStageOpenFixedRing X s i))) =
      U.ι ≫ (etaleCurveStructure X s p).app i)
    (cV : V ⟶ Spec (.of (Polynomial (etaleStageOpenFixedRing X s i))))
    (hcV : cV ≫ Spec.map (CommRingCat.ofHom
        (Polynomial.C : (etaleStageOpenFixedRing X s i) →+*
          Polynomial (etaleStageOpenFixedRing X s i))) =
      j ≫ (U.ι ≫ (etaleCurveStructure X s p).app i))
    (hjπ : j ≫ π = cV ≫ projectiveLineXChart (etaleStageOpenFixedRing X s i))
    {Nchart : Scheme.{u}} [IrreducibleSpace Nchart]
    (r₀ : U.toScheme ⟶ Nchart) [Flat r₀]
    {W : Scheme.{u}} (eChart : W ⟶ Nchart) [IsOpenImmersion eChart] [Nonempty W]
    (cW : Limits.pullback r₀ eChart ⟶ Spec (.of (Polynomial (etaleStageOpenFixedRing X s i))))
    [Etale cW]
    (hcW : cW ≫ Spec.map (CommRingCat.ofHom
        (Polynomial.C : (etaleStageOpenFixedRing X s i) →+*
          Polynomial (etaleStageOpenFixedRing X s i))) =
      Limits.pullback.fst r₀ eChart ≫ (U.ι ≫ (etaleCurveStructure X s p).app i))
    (heChart : Limits.pullback.fst r₀ eChart ≫ π =
      cW ≫ projectiveLineXChart (etaleStageOpenFixedRing X s i))
    (hd : Set.range d = (Set.range j)ᶜ)
    (σV τV : ∀ ℓ : Over i, ((smallEtaleNeighborhoodToSmooth X s).obj ℓ.left).left ⟶
      (etaleStageOpenBoundaryDiagram X s p i U j).obj ℓ)
    (hσV : ∀ ℓ, σV ℓ ≫ (etaleStageOpenBoundaryMap X s p i U j).app ℓ =
      etaleStageOpenSection X s p i U σ hσ ℓ)
    (hτV : ∀ ℓ, τV ℓ ≫ (etaleStageOpenBoundaryMap X s p i U j).app ℓ =
      etaleStageOpenSection X s p i U τ hτ ℓ)
    {T : SmoothSite (Spec (.of K))}
    (r : ∀ ℓ : Over i, (etaleStageOpenBoundaryDiagram X s p i U j).obj ℓ ⟶
      Limits.pullback ((smallEtaleNeighborhoodToSmooth X s).obj ℓ.left).hom T.hom)
    (hr : ∀ ℓ, r ℓ ≫
        Limits.pullback.fst ((smallEtaleNeighborhoodToSmooth X s).obj ℓ.left).hom T.hom =
      (etaleStageOpenBoundaryMap X s p i U j).app ℓ ≫
        (etaleStageOpenStructure X s p i U).app ℓ)
    (f g : ∀ ℓ : Over i, (smallEtaleNeighborhoodToSmooth X s).obj ℓ.left ⟶ T)
    (hf : ∀ ℓ, (f ℓ).left = σV ℓ ≫ r ℓ ≫
      Limits.pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj ℓ.left).hom T.hom)
    (hg : ∀ ℓ, (g ℓ).left = τV ℓ ≫ r ℓ ≫
      Limits.pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj ℓ.left).hom T.hom)
    (k : ℕ)
    (hn : ∀ (A : SmoothSite (Spec (.of K)))
      (z : PresheafWithTransfers.sections P ((Cor.graphFunctor K).obj A)), (k + 1) • z = 0) : Prop :=
  let I := Over i
  let C := etaleStageOpenDiagram X s p i U
  let B' := etaleStageOpenBoundaryDiagram X s p i U d
  let b := etaleStageOpenBoundaryMap X s p i U d
  let cB := etaleStageOpenBoundaryCone X s p i U d B hX
  let cC := etaleStageOpenCone X s p i U B hX
  let bLim := etaleStageOpenBoundaryLimitMap X s p i U d B hX
  let hb := etaleStageOpenBoundaryCone_square X s p i U d B hX
  let D := fun a => (etaleStageOpenSection X s p i U σ hσ a).ker
  let E := fun a => (etaleStageOpenSection X s p i U τ hτ a).ker
  let hDmap : ∀ {a d : I} (v : a ⟶ d), (D d).comap (C.map v) = D a :=
    fun {_ _} v => (etaleStageOpenSection_ker X s p i U σ hσ v).symm
  let hEmap : ∀ {a d : I} (v : a ⟶ d), (E d).comap (C.map v) = E a :=
    fun {_ _} v => (etaleStageOpenSection_ker X s p i U τ hτ v).symm
  let aD := etaleStageOpenSection_boundary_avoids X s p i U σ hσ d hdσ
  let aE := etaleStageOpenSection_boundary_avoids X s p i U τ hτ d hdτ
  letI _hD : ∀ a, IsEffectiveCartierDivisor (D a) :=
    fun a => etaleStageOpenSection_isEffectiveCartierDivisor X s p i U σ hσ j hσj a
  letI _hE : ∀ a, IsEffectiveCartierDivisor (E a) :=
    fun a => etaleStageOpenSection_isEffectiveCartierDivisor X s p i U τ hτ j hτj a
  letI _hFP : (differenceSheaf (D a₀) (E a₀)).IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible
      (C.obj a₀) _ (isInvertible_differenceSheaf (D a₀) (E a₀)).toAlgebraicGeometry
  ∀ (M : cC.pt.Modules)
    [_hM : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property M]
    (α : tensorPower cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property M ((k + 1 : ℕ) : ℤ) ≅
        (Scheme.Modules.pullback (cC.π.app a₀)).obj (differenceSheaf (D a₀) (E a₀)))
    (e₀ : (Scheme.Modules.pullback bLim).obj M ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (he₀ : tensorPowerCongr cB.pt.toRingedSpace.presheaf
      (structureSheafRing cB.pt.toRingedSpace).property _ _ e₀ (k + 1) =
        boundaryRootPowerIso bLim M ((Scheme.Modules.pullback (cC.π.app a₀)).obj (differenceSheaf
          (D a₀) (E a₀))) (k + 1) α
          (pullbackBoundaryTrivialization (cB.π.app a₀) (b.app a₀) bLim
            (cC.π.app a₀) (hb a₀) (differenceSheaf (D a₀) (E a₀)) (differenceSheafBoundaryIso (b.app
              a₀) (D a₀) (E a₀) (aD a₀) (aE a₀))))
    (N₀ : cC.pt.Modules)
    (hN₀ : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.sheaf.obj
      cC.pt.ringCatSheaf.property N₀)
    (a₀root : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor cC.pt.sheaf).obj M).obj N₀, ⊤))
    (b₀ : Γ(N₀, ⊤))
    (eN₀ : (Scheme.Modules.pullback bLim).obj N₀ ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (hb₀ : Scheme.Modules.Hom.app (X := cB.pt) eN₀.hom ⊤
      (pullbackGlobalSections bLim N₀ b₀) = (1 : Γ(cB.pt, ⊤)))
    (ha₀ : Scheme.Modules.Hom.app (X := cB.pt)
      (Scheme.Modules.pullbackTensorFrame bLim M N₀ e₀ eN₀).hom ⊤
      (pullbackGlobalSections bLim _ a₀root) = (1 : Γ(cB.pt, ⊤))),
  OriginalRootAuxiliaryFramesConsumerResult
    B' C b cB cC bLim hb D E hDmap hEmap aD aE a₀ M (k + 1) α e₀ he₀ N₀ hN₀ a₀root b₀ eN₀ hb₀ ha₀ →
  let Finish : ∀ (ℓ : I) (MR NR : (C.obj ℓ).Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (C.obj ℓ).toRingedSpace).property MR],
      (tensorPower (C.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (C.obj ℓ).toRingedSpace).property MR ((k + 1 : ℕ) : ℤ) ≅
          differenceSheaf (D ℓ) (E ℓ)) →
      ((Scheme.Modules.pullback (b.app ℓ)).obj MR ≅ SheafOfModules.unit (B'.obj ℓ).ringCatSheaf) →
      ((Scheme.Modules.pullback (b.app ℓ)).obj NR ≅ SheafOfModules.unit (B'.obj ℓ).ringCatSheaf) →
      Γ(((Stacks.SheafOfModules.Tensor.sheafTensor
        (C.obj ℓ).sheaf).obj MR).obj NR, ⊤) →
      Γ(NR, ⊤) → Prop := fun ℓ _MR _NR _hMR _αR _eR _eNR _aR _bR =>
    ∃ (Anew : EtaleNeighborhood X s.hom)
      (v : Anew ⟶ (smallEtaleNeighborhoodInclusion X s).obj ℓ.left),
      ((PresheafWithTransfers.toPresheaf K).obj P).map
          (((etaleNeighborhoodToSmooth X s.hom).map v) ≫ f ℓ).op =
        ((PresheafWithTransfers.toPresheaf K).obj P).map
          (((etaleNeighborhoodToSmooth X s.hom).map v) ≫ g ℓ).op
  OriginalRootAuxiliaryFramesConsumerResultWithFinal
    B' C b cB cC bLim hb D E hDmap hEmap aD aE a₀ M (k + 1) α e₀ he₀ N₀ hN₀ a₀root b₀ eN₀ hb₀ ha₀ Finish

/-- The actual refinement producer fills the continuation, not a compatibility assumption. -/
theorem etaleStageOpenRestrictionConsumerResult
    {K : Type u} [Field K] (P : PresheafWithTransfers.{v} K)
    (hP : PresheafWithTransfers.IsA1Invariant P)
    (X : SmoothSite (Spec (.of K)))
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    {Z : Scheme.{u}} (d : Z ⟶ U.toScheme)
    [IsLocallyNoetherian X.left] [IsProper p] [IsClosedImmersion U.ι]
    [IsClosedImmersion d]
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme (Spec (.of K))).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hτ : τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    [IsClosedImmersion σ] [IsClosedImmersion τ]
    [IsSeparated (U.ι ≫ (etaleCurveStructure X s p).app i)]
    {V : Scheme.{u}} [IsAffine V] (j : V ⟶ U.toScheme) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ (U.ι ≫ (etaleCurveStructure X s p).app i))]
    (hσj : Set.range σ ⊆ Set.range j) (hτj : Set.range τ ⊆ Set.range j)
    (hdσ : ∀ z : Z, d z ∉ Set.range σ) (hdτ : ∀ z : Z, d z ∉ Set.range τ)
    (a₀ : Over i)
    [IsNormal X.left] [IsNormal N]
    (hmark : etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a₀.left) ≫
          etaleStageOpenSection X s p i U σ hσ a₀ =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a₀.left) ≫
          etaleStageOpenSection X s p i U τ hτ a₀)
    (π : U.toScheme ⟶ projectiveLine (etaleStageOpenFixedRing X s i)) [IsFinite π]
    (hπ : π ≫ (projectiveLine (etaleStageOpenFixedRing X s i) ↘
        Spec (.of ↥(etaleStageOpenFixedRing X s i))) =
      U.ι ≫ (etaleCurveStructure X s p).app i)
    (cV : V ⟶ Spec (.of (Polynomial (etaleStageOpenFixedRing X s i))))
    (hcV : cV ≫ Spec.map (CommRingCat.ofHom
        (Polynomial.C : (etaleStageOpenFixedRing X s i) →+*
          Polynomial (etaleStageOpenFixedRing X s i))) =
      j ≫ (U.ι ≫ (etaleCurveStructure X s p).app i))
    (hjπ : j ≫ π = cV ≫ projectiveLineXChart (etaleStageOpenFixedRing X s i))
    {Nchart : Scheme.{u}} [IrreducibleSpace Nchart]
    (r₀ : U.toScheme ⟶ Nchart) [Flat r₀]
    {W : Scheme.{u}} (eChart : W ⟶ Nchart) [IsOpenImmersion eChart] [Nonempty W]
    (cW : Limits.pullback r₀ eChart ⟶ Spec (.of (Polynomial (etaleStageOpenFixedRing X s i))))
    [Etale cW]
    (hcW : cW ≫ Spec.map (CommRingCat.ofHom
        (Polynomial.C : (etaleStageOpenFixedRing X s i) →+*
          Polynomial (etaleStageOpenFixedRing X s i))) =
      Limits.pullback.fst r₀ eChart ≫ (U.ι ≫ (etaleCurveStructure X s p).app i))
    (heChart : Limits.pullback.fst r₀ eChart ≫ π =
      cW ≫ projectiveLineXChart (etaleStageOpenFixedRing X s i))
    (hd : Set.range d = (Set.range j)ᶜ)
    (σV τV : ∀ ℓ : Over i, ((smallEtaleNeighborhoodToSmooth X s).obj ℓ.left).left ⟶
      (etaleStageOpenBoundaryDiagram X s p i U j).obj ℓ)
    (hσV : ∀ ℓ, σV ℓ ≫ (etaleStageOpenBoundaryMap X s p i U j).app ℓ =
      etaleStageOpenSection X s p i U σ hσ ℓ)
    (hτV : ∀ ℓ, τV ℓ ≫ (etaleStageOpenBoundaryMap X s p i U j).app ℓ =
      etaleStageOpenSection X s p i U τ hτ ℓ)
    {T : SmoothSite (Spec (.of K))}
    (r : ∀ ℓ : Over i, (etaleStageOpenBoundaryDiagram X s p i U j).obj ℓ ⟶
      Limits.pullback ((smallEtaleNeighborhoodToSmooth X s).obj ℓ.left).hom T.hom)
    (hr : ∀ ℓ, r ℓ ≫
        Limits.pullback.fst ((smallEtaleNeighborhoodToSmooth X s).obj ℓ.left).hom T.hom =
      (etaleStageOpenBoundaryMap X s p i U j).app ℓ ≫
        (etaleStageOpenStructure X s p i U).app ℓ)
    (f g : ∀ ℓ : Over i, (smallEtaleNeighborhoodToSmooth X s).obj ℓ.left ⟶ T)
    (hf : ∀ ℓ, (f ℓ).left = σV ℓ ≫ r ℓ ≫
      Limits.pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj ℓ.left).hom T.hom)
    (hg : ∀ ℓ, (g ℓ).left = τV ℓ ≫ r ℓ ≫
      Limits.pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj ℓ.left).hom T.hom)
    (k : ℕ)
    (hn : ∀ (A : SmoothSite (Spec (.of K)))
      (z : PresheafWithTransfers.sections P ((Cor.graphFunctor K).obj A)), (k + 1) • z = 0) :
    EtaleStageOpenRestrictionConsumerResult P hP X s p i U d B hX
      σ τ hσ hτ j hσj hτj hdσ hdτ a₀ hmark
      π hπ cV hcV hjπ r₀ eChart cW hcW heChart hd
      σV τV hσV hτV r hr f g hf hg k hn := by
  let I := Over i
  let C := etaleStageOpenDiagram X s p i U
  let B' := etaleStageOpenBoundaryDiagram X s p i U d
  let b := etaleStageOpenBoundaryMap X s p i U d
  let cB := etaleStageOpenBoundaryCone X s p i U d B hX
  let cC := etaleStageOpenCone X s p i U B hX
  let bLim := etaleStageOpenBoundaryLimitMap X s p i U d B hX
  let hb := etaleStageOpenBoundaryCone_square X s p i U d B hX
  let D := fun a => (etaleStageOpenSection X s p i U σ hσ a).ker
  let E := fun a => (etaleStageOpenSection X s p i U τ hτ a).ker
  let hDmap : ∀ {a d : I} (v : a ⟶ d), (D d).comap (C.map v) = D a :=
    fun {_ _} v => (etaleStageOpenSection_ker X s p i U σ hσ v).symm
  let hEmap : ∀ {a d : I} (v : a ⟶ d), (E d).comap (C.map v) = E a :=
    fun {_ _} v => (etaleStageOpenSection_ker X s p i U τ hτ v).symm
  let aD := etaleStageOpenSection_boundary_avoids X s p i U σ hσ d hdσ
  let aE := etaleStageOpenSection_boundary_avoids X s p i U τ hτ d hdτ
  let _hD : ∀ a, IsEffectiveCartierDivisor (D a) :=
    fun a => etaleStageOpenSection_isEffectiveCartierDivisor X s p i U σ hσ j hσj a
  let _hE : ∀ a, IsEffectiveCartierDivisor (E a) :=
    fun a => etaleStageOpenSection_isEffectiveCartierDivisor X s p i U τ hτ j hτj a
  let _hFP : (differenceSheaf (D a₀) (E a₀)).IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible
      (C.obj a₀) _ (isInvertible_differenceSheaf (D a₀) (E a₀)).toAlgebraicGeometry
  intro M hM α e₀ he₀ N₀ hN₀ a₀root b₀ eN₀ hb₀ ha₀ H
  let Finish : ∀ (ℓ : I) (MR NR : (C.obj ℓ).Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (C.obj ℓ).toRingedSpace).property MR],
      (tensorPower (C.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (C.obj ℓ).toRingedSpace).property MR ((k + 1 : ℕ) : ℤ) ≅
          differenceSheaf (D ℓ) (E ℓ)) →
      ((Scheme.Modules.pullback (b.app ℓ)).obj MR ≅ SheafOfModules.unit (B'.obj ℓ).ringCatSheaf) →
      ((Scheme.Modules.pullback (b.app ℓ)).obj NR ≅ SheafOfModules.unit (B'.obj ℓ).ringCatSheaf) →
      Γ(((Stacks.SheafOfModules.Tensor.sheafTensor
        (C.obj ℓ).sheaf).obj MR).obj NR, ⊤) →
      Γ(NR, ⊤) → Prop := fun ℓ _MR _NR _hMR _αR _eR _eNR _aR _bR =>
    ∃ (Anew : EtaleNeighborhood X s.hom)
      (v : Anew ⟶ (smallEtaleNeighborhoodInclusion X s).obj ℓ.left),
      ((PresheafWithTransfers.toPresheaf K).obj P).map
          (((etaleNeighborhoodToSmooth X s.hom).map v) ≫ f ℓ).op =
        ((PresheafWithTransfers.toPresheaf K).obj P).map
          (((etaleNeighborhoodToSmooth X s.hom).map v) ≫ g ℓ).op
  apply originalRootAuxiliaryFramesConsumerResult_withFinal_invertiblePair
    B' C b cB cC bLim hb D E hDmap hEmap aD aE a₀ M (k + 1) α e₀ he₀ N₀ hN₀ a₀root b₀ eN₀ hb₀ ha₀ Finish H
  intro ℓ MR NR hMR hNR hMRStacks hNRStacks αR eR eNR aR bR hpow haR hbR
  obtain ⟨Anew, v, hAff, hInt, hNoeth, hG, hGC, hCN, hCNoeth,
      σ₂, τ₂, hσ₂, hτ₂, hEq⟩ :=
    exists_etaleStageOpen_same_root_restriction P hP X s p i U ℓ
      π hπ j cV hcV hjπ r₀ eChart cW hcW heChart d hd
      (etaleStageOpenSection X s p i U σ hσ ℓ)
      (etaleStageOpenSection X s p i U τ hτ ℓ)
      (etaleStageOpenSection_structure X s p i U σ hσ ℓ)
      (etaleStageOpenSection_structure X s p i U τ hτ ℓ)
      (etaleStageOpenSection_same_marking_of_one X s p i U B hX σ τ hσ hτ a₀ ℓ hmark)
      (σV ℓ) (τV ℓ) (hσV ℓ) (hτV ℓ) (r ℓ) (hr ℓ) (f ℓ) (g ℓ) (hf ℓ) (hg ℓ)
      (aD ℓ) (aE ℓ) MR NR k hn αR eR eNR aR bR hpow haR hbR
  exact ⟨Anew, v, hEq⟩

end AlgebraicGeometry.Scheme.SmoothSite
