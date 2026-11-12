/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenSectionDivisors
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenBoundaryNoetherian
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootAuxiliaryFramesConsumerResultWithFinal
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ActualStageRootAuxiliaryRefinement
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenAllMarkings
public import Colib.AlgebraicGeometry.Divisors.DifferenceSheafPicard

/-! # The actual component system supplied to consumer-normalized descent

This theorem discharges all diagram and ideal-family inputs and returns the
named full consumer-normalized proposition. Its
remaining arguments are exactly the original limit root and auxiliary data of
the existing theorem, and its result retains every original recovery equation.
The initial object `a₀` is an actual object of `Over i`, not silently identified
with the fixed open `U`.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules Stacks.Divisors
open Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace AlgebraicGeometry.Scheme.SmoothSite

local instance actualRefinedResultPullbackInvertible
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [_hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M hM

/-- The original Result, with an actual same-witness refinement inside its final leaf. -/
def EtaleStageOpenRefinedConsumerResult
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    {Z : Scheme.{u}} (d : Z ⟶ U.toScheme)
    [IsLocallyNoetherian X.left] [IsProper p] [IsClosedImmersion U.ι]
    [IsClosedImmersion d]
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hτ : τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    [IsClosedImmersion σ] [IsClosedImmersion τ]
    [IsSeparated (U.ι ≫ (etaleCurveStructure X s p).app i)]
    {V : Scheme.{u}} (j : V ⟶ U.toScheme) [IsOpenImmersion j]
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
          etaleStageOpenSection X s p i U τ hτ a₀) : Prop :=
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
      (structureSheafRing cC.pt.toRingedSpace).property M] (n : ℕ)
    (α : tensorPower cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property M (n : ℤ) ≅
        (Scheme.Modules.pullback (cC.π.app a₀)).obj (differenceSheaf (D a₀) (E a₀)))
    (e₀ : (Scheme.Modules.pullback bLim).obj M ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (he₀ : tensorPowerCongr cB.pt.toRingedSpace.presheaf
      (structureSheafRing cB.pt.toRingedSpace).property _ _ e₀ n =
        boundaryRootPowerIso bLim M ((Scheme.Modules.pullback (cC.π.app a₀)).obj (differenceSheaf
          (D a₀) (E a₀))) n α
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
    B' C b cB cC bLim hb D E hDmap hEmap aD aE a₀ M n α e₀ he₀ N₀ hN₀ a₀root b₀ eN₀ hb₀ ha₀ →
  let Finish : ∀ (ℓ : I) (MR NR : (C.obj ℓ).Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (C.obj ℓ).toRingedSpace).property MR],
      (tensorPower (C.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (C.obj ℓ).toRingedSpace).property MR (n : ℤ) ≅
          differenceSheaf (D ℓ) (E ℓ)) →
      ((Scheme.Modules.pullback (b.app ℓ)).obj MR ≅ SheafOfModules.unit (B'.obj ℓ).ringCatSheaf) →
      ((Scheme.Modules.pullback (b.app ℓ)).obj NR ≅ SheafOfModules.unit (B'.obj ℓ).ringCatSheaf) →
      Γ(((Stacks.SheafOfModules.Tensor.sheafTensor
        (C.obj ℓ).sheaf).obj MR).obj NR, ⊤) →
      Γ(NR, ⊤) → Prop := fun ℓ MR NR _hMR αR eR eNR aR bR =>
    ActualStageRootAuxiliaryRefinement X s p i U ℓ
      (etaleStageOpenSection X s p i U σ hσ ℓ)
      (etaleStageOpenSection X s p i U τ hτ ℓ)
      (etaleStageOpenSection_structure X s p i U σ hσ ℓ)
      (etaleStageOpenSection_structure X s p i U τ hτ ℓ)
      (etaleStageOpenSection_same_marking_of_one X s p i U B hX σ τ hσ hτ a₀ ℓ hmark)
      (b.app ℓ) (aD ℓ) (aE ℓ) MR NR n αR eR eNR aR bR
  OriginalRootAuxiliaryFramesConsumerResultWithFinal
    B' C b cB cC bLim hb D E hDmap hEmap aD aE a₀ M n α e₀ he₀ N₀ hN₀ a₀root b₀ eN₀ hb₀ ha₀ Finish

/-- The actual refinement producer fills the continuation, not a compatibility assumption. -/
theorem etaleStageOpenRefinedConsumerResult
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    {Z : Scheme.{u}} (d : Z ⟶ U.toScheme)
    [IsLocallyNoetherian X.left] [IsProper p] [IsClosedImmersion U.ι]
    [IsClosedImmersion d]
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hτ : τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    [IsClosedImmersion σ] [IsClosedImmersion τ]
    [IsSeparated (U.ι ≫ (etaleCurveStructure X s p).app i)]
    {V : Scheme.{u}} (j : V ⟶ U.toScheme) [IsOpenImmersion j]
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
          etaleStageOpenSection X s p i U τ hτ a₀) :
    EtaleStageOpenRefinedConsumerResult X s p i U d B hX σ τ hσ hτ j hσj hτj hdσ hdτ a₀ hmark := by
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
  intro M hM n α e₀ he₀ N₀ hN₀ a₀root b₀ eN₀ hb₀ ha₀ H
  let Finish : ∀ (ℓ : I) (MR NR : (C.obj ℓ).Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (C.obj ℓ).toRingedSpace).property MR],
      (tensorPower (C.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (C.obj ℓ).toRingedSpace).property MR (n : ℤ) ≅
          differenceSheaf (D ℓ) (E ℓ)) →
      ((Scheme.Modules.pullback (b.app ℓ)).obj MR ≅ SheafOfModules.unit (B'.obj ℓ).ringCatSheaf) →
      ((Scheme.Modules.pullback (b.app ℓ)).obj NR ≅ SheafOfModules.unit (B'.obj ℓ).ringCatSheaf) →
      Γ(((Stacks.SheafOfModules.Tensor.sheafTensor
        (C.obj ℓ).sheaf).obj MR).obj NR, ⊤) →
      Γ(NR, ⊤) → Prop := fun ℓ MR NR hMR αR eR eNR aR bR =>
    ActualStageRootAuxiliaryRefinement X s p i U ℓ
      (etaleStageOpenSection X s p i U σ hσ ℓ)
      (etaleStageOpenSection X s p i U τ hτ ℓ)
      (etaleStageOpenSection_structure X s p i U σ hσ ℓ)
      (etaleStageOpenSection_structure X s p i U τ hτ ℓ)
      (etaleStageOpenSection_same_marking_of_one X s p i U B hX σ τ hσ hτ a₀ ℓ hmark)
      (b.app ℓ) (aD ℓ) (aE ℓ) MR NR n αR eR eNR aR bR
  apply originalRootAuxiliaryFramesConsumerResult_withFinal
    B' C b cB cC bLim hb D E hDmap hEmap aD aE a₀ M n α e₀ he₀ N₀ hN₀ a₀root b₀ eN₀ hb₀ ha₀ Finish H
  intro ℓ MR NR hMR αR eR eNR aR bR hpow haR hbR
  exact actualStageRootAuxiliaryRefinement X s p i U ℓ
    (etaleStageOpenSection X s p i U σ hσ ℓ)
    (etaleStageOpenSection X s p i U τ hτ ℓ)
    (etaleStageOpenSection_structure X s p i U σ hσ ℓ)
    (etaleStageOpenSection_structure X s p i U τ hτ ℓ)
    (etaleStageOpenSection_same_marking_of_one X s p i U B hX σ τ hσ hτ a₀ ℓ hmark)
    (b.app ℓ) (aD ℓ) (aE ℓ) MR NR n αR eR eNR aR bR hpow haR hbR

end AlgebraicGeometry.Scheme.SmoothSite
