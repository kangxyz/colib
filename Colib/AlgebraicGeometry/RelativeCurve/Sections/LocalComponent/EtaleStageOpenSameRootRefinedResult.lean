/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenSameRootConsumerResult
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenRefinedConsumerResult

/-! # One original supplier, the same descent witnesses, and actual integral refinement

The original supplier is called once. Its root, power isomorphism, frame,
auxiliary module, sections, boundary equations and nonzero proofs are re-used
unchanged. Inside its named four-layer descent result, the final stage receives
the actual integral-base and marked-component refinement. No external root,
Finish producer or final compatibility assumption is introduced.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
open Stacks.Divisors Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace AlgebraicGeometry.Scheme.SmoothSite

local instance actualSameRootRefinedRingedInvertible (X : Scheme.{u}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance actualSameRootRefinedPullbackInvertible {X Y : Scheme.{u}}
    (b : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      ((Scheme.Modules.pullback b).obj M) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj b.toLRSHom.toShHom M)

local instance actualSameRootRefinedUnitInvertible (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)



/-- The entire original supplier output with actual refinement inside the same
four layers of descended witnesses. This is a named proposition, not a new input. -/
def EtaleStageOpenSameRootRefinedResult
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    [IsLocallyNoetherian X.left] [IsProper p] [IsNormal X.left] [IsNormal N]
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    [IsClosedImmersion U.ι]
    [IsSeparated (U.ι ≫ (etaleCurveStructure X s p).app i)]
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    [IsLocallyNoetherian (etaleCurveCone X B hX s p).pt]
    [IsNormal (etaleCurveCone X B hX s p).pt]
    (x : (etaleCurveCone X B hX s p).pt)
    (_hpre : (etaleCurveCone X B hX s p).π.app i ⁻¹ᵁ U = normalComponentOpen x)
    (_hp : IsProjectiveMorphism p)
    {V Z : Scheme.{u}}
    (j : V ⟶ U.toScheme) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ U.ι ≫ (etaleCurveStructure X s p).app i)]
    (d : Z ⟶ U.toScheme)
    (hd : Set.range d = (Set.range j)ᶜ)
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hτ : τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hσj : Set.range σ ⊆ Set.range j) (hτj : Set.range τ ⊆ Set.range j)
    (a0 : Over i)
    (hmark : etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a0.left) ≫
          etaleStageOpenSection X s p i U σ hσ a0 =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a0.left) ≫
          etaleStageOpenSection X s p i U τ hτ a0)
    {n : ℕ} (_hn0 : n ≠ 0) (_hn : IsUnit (n : ↥(etaleLocalRing B X.left hX s))) : Prop :=
  let I := Over i
  let C := etaleStageOpenDiagram X s p i U
  let B' := etaleStageOpenBoundaryDiagram X s p i U d
  let b := etaleStageOpenBoundaryMap X s p i U d
  let cB := etaleStageOpenBoundaryCone X s p i U d B hX
  let cC := etaleStageOpenCone X s p i U B hX
  let bLim := etaleStageOpenBoundaryLimitMap X s p i U d B hX
  let hb := etaleStageOpenBoundaryCone_square X s p i U d B hX
  letI _hσclosed : IsClosedImmersion σ := by
    let : IsClosedImmersion (σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i)) := by
      rw [hσ]
      infer_instance
    exact IsClosedImmersion.of_comp σ (U.ι ≫ (etaleCurveStructure X s p).app i)
  letI _hτclosed : IsClosedImmersion τ := by
    let : IsClosedImmersion (τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i)) := by
      rw [hτ]
      infer_instance
    exact IsClosedImmersion.of_comp τ (U.ι ≫ (etaleCurveStructure X s p).app i)
  let hdσ : ∀ z : Z, d z ∉ Set.range σ := by
    intro z hz
    have hdz : d z ∈ Set.range d := ⟨z, rfl⟩
    rw [hd] at hdz
    exact hdz (hσj hz)
  let hdτ : ∀ z : Z, d z ∉ Set.range τ := by
    intro z hz
    have hdz : d z ∈ Set.range d := ⟨z, rfl⟩
    rw [hd] at hdz
    exact hdz (hτj hz)
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
  let τStage := differenceSheafBoundaryIso (b.app a0) (D a0) (E a0) (aD a0) (aE a0)
  let τLim := pullbackBoundaryTrivialization (cB.π.app a0) (b.app a0) bLim
    (cC.π.app a0) (hb a0) (differenceSheaf (D a0) (E a0)) τStage
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
      (etaleStageOpenSection_same_marking_of_one X s p i U B hX σ τ hσ hτ a0 ℓ hmark)
      (b.app ℓ) (aD ℓ) (aE ℓ) MR NR n αR eR eNR aR bR
  ∃ (M : cC.pt.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible cC.pt.presheaf cC.pt.ringCatIsSheaf M),
    let _ := hM
    let _ : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property M := hM.toAlgebraicGeometry
    ∃ (α : tensorPower cC.pt.toRingedSpace.presheaf
        (structureSheafRing cC.pt.toRingedSpace).property M (n : ℤ) ≅
        (Scheme.Modules.pullback (cC.π.app a0)).obj (differenceSheaf (D a0) (E a0)))
      (e : (Scheme.Modules.pullback bLim).obj M ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
      (he : tensorPowerCongr cB.pt.presheaf (ringSheafCond cB.pt) _ _ e n =
        boundaryRootPowerIso bLim M _ n α τLim)
      (Naux : cC.pt.Modules)
      (hNaux : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.sheaf.obj
        cC.pt.ringCatSheaf.property Naux)
      (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor cC.pt.sheaf).obj M).obj Naux, ⊤))
      (bN : Γ(Naux, ⊤))
      (eN : (Scheme.Modules.pullback bLim).obj Naux ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
      (hbN : Scheme.Modules.Hom.app (X := cB.pt) eN.hom ⊤ (pullbackGlobalSections bLim Naux bN) =
        (1 : Γ(cB.pt, ⊤)))
      (haB : Scheme.Modules.Hom.app (X := cB.pt)
        (Scheme.Modules.pullbackTensorFrame bLim M Naux e eN).hom ⊤
        (pullbackGlobalSections bLim _ a) = (1 : Γ(cB.pt, ⊤))),
      a ≠ 0 ∧ bN ≠ 0 ∧
      OriginalRootAuxiliaryFramesConsumerResultWithFinal
        B' C b cB cC bLim hb D E hDmap hEmap aD aE a0
        M n α e he Naux hNaux a bN eN hbN haB Finish

/-- Supply and descend the original root once, then refine those exact witnesses. -/
theorem etaleStageOpen_exists_same_root_refined_result
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    [IsLocallyNoetherian X.left] [IsProper p] [IsNormal X.left] [IsNormal N]
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    [IsClosedImmersion U.ι]
    [IsSeparated (U.ι ≫ (etaleCurveStructure X s p).app i)]
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    [IsLocallyNoetherian (etaleCurveCone X B hX s p).pt]
    [IsNormal (etaleCurveCone X B hX s p).pt]
    (x : (etaleCurveCone X B hX s p).pt)
    (hpre : (etaleCurveCone X B hX s p).π.app i ⁻¹ᵁ U = normalComponentOpen x)
    (hp : IsProjectiveMorphism p)
    {V Z : Scheme.{u}} [IsAffine V]
    (j : V ⟶ U.toScheme) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ U.ι ≫ (etaleCurveStructure X s p).app i)]
    (d : Z ⟶ U.toScheme) [IsClosedImmersion d]
    [IsFinite (d ≫ U.ι ≫ (etaleCurveStructure X s p).app i)]
    (hd : Set.range d = (Set.range j)ᶜ)
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hτ : τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hσj : Set.range σ ⊆ Set.range j) (hτj : Set.range τ ⊆ Set.range j)
    (a0 : Over i)
    (hmark : etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a0.left) ≫
          etaleStageOpenSection X s p i U σ hσ a0 =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a0.left) ≫
          etaleStageOpenSection X s p i U τ hτ a0)
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : ↥(etaleLocalRing B X.left hX s))) :
    EtaleStageOpenSameRootRefinedResult X s p i U B hX x hpre hp j d hd
      σ τ hσ hτ hσj hτj a0 hmark hn0 hn := by
  let I := Over i
  let C := etaleStageOpenDiagram X s p i U
  let B' := etaleStageOpenBoundaryDiagram X s p i U d
  let b := etaleStageOpenBoundaryMap X s p i U d
  let cB := etaleStageOpenBoundaryCone X s p i U d B hX
  let cC := etaleStageOpenCone X s p i U B hX
  let bLim := etaleStageOpenBoundaryLimitMap X s p i U d B hX
  let hb := etaleStageOpenBoundaryCone_square X s p i U d B hX
  let _hσclosed : IsClosedImmersion σ := by
    let : IsClosedImmersion (σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i)) := by
      rw [hσ]
      infer_instance
    exact IsClosedImmersion.of_comp σ (U.ι ≫ (etaleCurveStructure X s p).app i)
  let _hτclosed : IsClosedImmersion τ := by
    let : IsClosedImmersion (τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i)) := by
      rw [hτ]
      infer_instance
    exact IsClosedImmersion.of_comp τ (U.ι ≫ (etaleCurveStructure X s p).app i)
  let hdσ : ∀ z : Z, d z ∉ Set.range σ := by
    intro z hz
    have hdz : d z ∈ Set.range d := ⟨z, rfl⟩
    rw [hd] at hdz
    exact hdz (hσj hz)
  let hdτ : ∀ z : Z, d z ∉ Set.range τ := by
    intro z hz
    have hdz : d z ∈ Set.range d := ⟨z, rfl⟩
    rw [hd] at hdz
    exact hdz (hτj hz)
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
  let τStage := differenceSheafBoundaryIso (b.app a0) (D a0) (E a0) (aD a0) (aE a0)
  let τLim := pullbackBoundaryTrivialization (cB.π.app a0) (b.app a0) bLim
    (cC.π.app a0) (hb a0) (differenceSheaf (D a0) (E a0)) τStage
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
      (etaleStageOpenSection_same_marking_of_one X s p i U B hX σ τ hσ hτ a0 ℓ hmark)
      (b.app ℓ) (aD ℓ) (aE ℓ) MR NR n αR eR eNR aR bR
  obtain ⟨M, hM, α, e, he, Naux, hNaux, a, bN, eN, hbN, haB, ha, hbnonzero, H⟩ :=
    etaleStageOpen_exists_same_root_consumer_result
      X s p i U B hX x hpre hp j d hd σ τ hσ hτ hσj hτj a0 hmark hn0 hn
  let := hM
  let : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property M := hM.toAlgebraicGeometry
  refine ⟨M, hM, α, e, he, Naux, hNaux, a, bN, eN, hbN, haB, ha, hbnonzero, ?_⟩
  exact (etaleStageOpenRefinedConsumerResult X s p i U d B hX σ τ hσ hτ
    j hσj hτj hdσ hdτ a0 hmark) M n α e he Naux hNaux a bN eN hbN haB H

end AlgebraicGeometry.Scheme.SmoothSite
