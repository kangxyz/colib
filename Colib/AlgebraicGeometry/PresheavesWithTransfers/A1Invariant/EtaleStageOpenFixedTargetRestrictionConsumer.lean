/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.EtaleStageOpenRestrictionConsumerResult
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenRetainedTargetFamily

/-! # Same-result restriction from the fixed original retained target

The input maps and retained section factors live only at the fixed original
stage. Every subsequent retained factor and target map is the actual Cartesian
construction. The original root and full descent Result remain the inputs of
the unchanged consumer proposition, and its final neighborhood witnesses and
all recovery data are retained unchanged.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules Stacks.Divisors
open Stacks.SheafOfModules.Invertible Stacks.AlgebraicGeometry.ModuleLimits
universe u v
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Fill the restriction consumer with the actual retained-target family of the
two fixed maps. No arbitrary stage family or final compatibility producer is input. -/
theorem etaleStageOpenRestrictionConsumerResult_of_fixed_target
    {K : Type u} [Field K] (P : PresheafWithTransfers.{v} K)
    (hP : PresheafWithTransfers.IsA1Invariant P)
    (X : SmoothSite (Spec (.of K)))
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    {Z : Scheme.{u}} (d : Z ⟶ U.toScheme)
    [IsLocallyNoetherian X.left] [IsProper p] [IsClosedImmersion U.ι]
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
      (z : PresheafWithTransfers.sections P ((Cor.graphFunctor K).obj A)), (k + 1) • z = 0) :
    EtaleStageOpenRestrictionConsumerResult
    P hP X s p i U d B hX σ τ hσ hτ j hσj hτj hdσ hdτ a₀ hmark
    π hπ cV hcV hjπ r₀ eChart cW hcW heChart hd
    (etaleStageOpenRetainedSection X s p i U j σ hσ σVFixed hσVFixed)
    (etaleStageOpenRetainedSection X s p i U j τ hτ τVFixed hτVFixed)
    (etaleStageOpenRetainedSection_map X s p i U j σ hσ σVFixed hσVFixed)
    (etaleStageOpenRetainedSection_map X s p i U j τ hτ τVFixed hτVFixed)
    (etaleStageOpenRetainedTarget X s p i U j T rFixed hrFixed)
    (etaleStageOpenRetainedTarget_fst X s p i U j T rFixed hrFixed)
    (fun ℓ => (smallEtaleNeighborhoodToSmooth X s).map ℓ.hom ≫ f₀)
    (fun ℓ => (smallEtaleNeighborhoodToSmooth X s).map ℓ.hom ≫ g₀)
    (etaleStageOpenRetainedSection_target X s p i U j T rFixed hrFixed
      σ hσ σVFixed hσVFixed f₀ hf₀)
    (etaleStageOpenRetainedSection_target X s p i U j T rFixed hrFixed
      τ hτ τVFixed hτVFixed g₀ hg₀) k hn := by
  exact etaleStageOpenRestrictionConsumerResult
    P hP X s p i U d B hX σ τ hσ hτ j hσj hτj hdσ hdτ a₀ hmark
    π hπ cV hcV hjπ r₀ eChart cW hcW heChart hd
    (etaleStageOpenRetainedSection X s p i U j σ hσ σVFixed hσVFixed)
    (etaleStageOpenRetainedSection X s p i U j τ hτ τVFixed hτVFixed)
    (etaleStageOpenRetainedSection_map X s p i U j σ hσ σVFixed hσVFixed)
    (etaleStageOpenRetainedSection_map X s p i U j τ hτ τVFixed hτVFixed)
    (etaleStageOpenRetainedTarget X s p i U j T rFixed hrFixed)
    (etaleStageOpenRetainedTarget_fst X s p i U j T rFixed hrFixed)
    (fun ℓ => (smallEtaleNeighborhoodToSmooth X s).map ℓ.hom ≫ f₀)
    (fun ℓ => (smallEtaleNeighborhoodToSmooth X s).map ℓ.hom ≫ g₀)
    (etaleStageOpenRetainedSection_target X s p i U j T rFixed hrFixed
      σ hσ σVFixed hσVFixed f₀ hf₀)
    (etaleStageOpenRetainedSection_target X s p i U j T rFixed hrFixed
      τ hτ τVFixed hτVFixed g₀ hg₀) k hn

end AlgebraicGeometry.Scheme.SmoothSite
