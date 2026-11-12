/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.EtaleStageOpenFixedTargetRestrictionConsumer
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenSameRootConsumerResult
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootAuxiliaryFramesConsumerExistenceElim

/-! # The actual same-root producer followed by fixed-target restriction

Select the original root and auxiliary pair once. Their unchanged full descent
Result is passed to the actual fixed-target continuation. The final neighborhood
and transition below are precisely those supplied in that Result's final leaf.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules Stacks.Divisors
open Stacks.SheafOfModules.Invertible Stacks.AlgebraicGeometry.ModuleLimits
universe u v
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Produce and consume the same root, giving equality for the two fixed original maps. -/
theorem exists_etaleStageOpen_fixed_target_restriction
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
    (σVFixed τVFixed : ((smallEtaleNeighborhoodToSmooth X s).obj i).left ⟶ V)
    (hσVFixed : σVFixed ≫ j = σ) (hτVFixed : τVFixed ≫ j = τ)
    {T : SmoothSite (Spec (.of K))}
    (rFixed : V ⟶ Limits.pullback ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom)
    (hrFixed : rFixed ≫
        Limits.pullback.fst ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom =
      j ≫ U.ι ≫ (etaleCurveStructure X s p).app i)
    (f₀ g₀ : (smallEtaleNeighborhoodToSmooth X s).obj i ⟶ T)
    (hf₀ : f₀.left = σVFixed ≫ rFixed ≫
      Limits.pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom)
    (hg₀ : g₀.left = τVFixed ≫ rFixed ≫
      Limits.pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom)
    (k : ℕ)
    (hn : ∀ (A : SmoothSite (Spec (.of K)))
      (z : PresheafWithTransfers.sections P ((Cor.graphFunctor K).obj A)), (k + 1) • z = 0)
    [IsLocallyNoetherian (etaleCurveCone X B hX s p).pt]
    [IsNormal (etaleCurveCone X B hX s p).pt]
    (x : (etaleCurveCone X B hX s p).pt)
    (hpre : (etaleCurveCone X B hX s p).π.app i ⁻¹ᵁ U = normalComponentOpen x)
    (hp : IsProjectiveMorphism p)
    [IsFinite (d ≫ U.ι ≫ (etaleCurveStructure X s p).app i)]
    (hnUnit : IsUnit ((k + 1 : ℕ) : ↥(etaleLocalRing B X.left hX s))) :
    ∃ (ℓ : Over i) (Anew : EtaleNeighborhood X s.hom)
      (v : Anew ⟶ (smallEtaleNeighborhoodInclusion X s).obj ℓ.left),
      ((PresheafWithTransfers.toPresheaf K).obj P).map
          (((etaleNeighborhoodToSmooth X s.hom).map v) ≫
            ((smallEtaleNeighborhoodToSmooth X s).map ℓ.hom ≫ f₀)).op =
        ((PresheafWithTransfers.toPresheaf K).obj P).map
          (((etaleNeighborhoodToSmooth X s.hom).map v) ≫
            ((smallEtaleNeighborhoodToSmooth X s).map ℓ.hom ≫ g₀)).op := by
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
  have hExist := etaleStageOpen_exists_same_root_consumer_result
    X s p i U B hX x hpre hp j d hd σ τ hσ hτ hσj hτj a₀ hmark
    (Nat.succ_ne_zero k) hnUnit
  have hFixed := etaleStageOpenRestrictionConsumerResult_of_fixed_target
    P hP X s p i U d B hX σ τ hσ hτ j hσj hτj hdσ hdτ a₀ hmark
    π hπ cV hcV hjπ r₀ eChart cW hcW heChart hd
    σVFixed τVFixed hσVFixed hτVFixed rFixed hrFixed f₀ g₀ hf₀ hg₀ k hn
  apply originalRootAuxiliaryFramesConsumerExistence_exists_finish
    B' C b cB cC bLim hb D E hDmap hEmap aD aE a₀ (k + 1)
    (fun ℓ => ∃ (Anew : EtaleNeighborhood X s.hom)
      (v : Anew ⟶ (smallEtaleNeighborhoodInclusion X s).obj ℓ.left),
      ((PresheafWithTransfers.toPresheaf K).obj P).map
          (((etaleNeighborhoodToSmooth X s.hom).map v) ≫
            ((smallEtaleNeighborhoodToSmooth X s).map ℓ.hom ≫ f₀)).op =
        ((PresheafWithTransfers.toPresheaf K).obj P).map
          (((etaleNeighborhoodToSmooth X s.hom).map v) ≫
            ((smallEtaleNeighborhoodToSmooth X s).map ℓ.hom ≫ g₀)).op) hExist
  intro M hM α e he Naux hNaux a bN eN hbN haB hResult
  exact hFixed M α e he Naux hNaux a bN eN hbN haB hResult

end AlgebraicGeometry.Scheme.SmoothSite
