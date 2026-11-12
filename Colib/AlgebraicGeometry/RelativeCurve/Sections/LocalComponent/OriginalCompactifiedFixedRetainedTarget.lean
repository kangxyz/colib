/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleCurveOriginalRetainedSectionStages
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.FixedClopenRetainedTarget

/-! # Original compactified sections to the actual fixed retained target

All curve stages, the component, both sections and the retained target are
produced from the original compactification and original retained maps.
The original base is affine, as in the neighborhood-induction chart. No
component-preimage, component-membership or stage-family producer is assumed.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The literal original retained-stage map is the existing Cartesian boundary
base-change map; only its name differs. -/
theorem etaleCurveOriginalRetainedStageMap_isPullback
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N Y : Scheme.{u}} (p : N ⟶ X.left) (j : Y ⟶ N)
    (i : SmallEtaleNeighborhood X s) :
    IsPullback (etaleCurveOriginalRetainedStageMap X s p j i)
      (pullback.snd ((smallEtaleNeighborhoodOver X s).obj i).hom (j ≫ p))
      (pullback.snd ((smallEtaleNeighborhoodOver X s).obj i).hom p) j :=
  etaleBoundaryBaseChangeMap_isPullback ((smallEtaleNeighborhoodOver X s).obj i).hom p j

/-- From the original retained sections and target, produce the actual fixed
clopen and every input to the fixed-target stage-family construction. -/
theorem exists_original_compactified_fixed_retained_target
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S) [IsAffine X.left]
    (s : GeometricPoint X.left) {N Y : Scheme.{u}} (p : N ⟶ X.left)
    [IsNormal X.left] [IsLocallyNoetherian X.left] [IsNormal N] [IsProper p]
    (j : Y ⟶ N) [IsAffine Y] [IsOpenImmersion j]
    [hSmooth : SmoothOfRelativeDimension 1 (j ≫ p)]
    (σY τY : X.left ⟶ Y)
    (hσY : σY ≫ (j ≫ p) = 𝟙 X.left) (hτY : τY ≫ (j ≫ p) = 𝟙 X.left)
    (hmark : s.hom ≫ (σY ≫ j) = s.hom ≫ (τY ≫ j))
    {T : SmoothSite S} (t : Y ⟶ T.left)
    (ht : t ≫ T.hom = j ≫ p ≫ X.hom)
    (f g : X ⟶ T) (hf : f.left = σY ≫ t) (hg : g.left = τY ≫ t)
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    (i₀ : SmallEtaleNeighborhood X s) :
    let hσ := (Category.assoc σY j p).trans hσY
    let hτ := (Category.assoc τY j p).trans hτY
    let σ₀ := etaleCurveOriginalSectionStage X s p (σY ≫ j) hσ i₀
    let τ₀ := etaleCurveOriginalSectionStage X s p (τY ≫ j) hτ i₀
    let j₀ := etaleCurveOriginalRetainedStageMap X s p j i₀
    let t₀ := pullback.snd ((smallEtaleNeighborhoodOver X s).obj i₀).hom (j ≫ p) ≫ t
    let h₀ := etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i₀)
    ∃ (markL : Spec (.of s.residueField) ⟶ (etaleCurveCone X B hX s p).pt),
      markL ≫ pullback.fst (strictHenselizationToBase B X.left hX s) p =
        geometricPointToStrictHenselization B X.left hX s ∧
      markL ≫ (etaleCurveCone X B hX s p).π.app i₀ =
        etaleNeighborhoodMark X s.hom
          ((smallEtaleNeighborhoodInclusion X s).obj i₀) ≫ σ₀ ∧
      ∃ (i : SmallEtaleNeighborhood X s) (e : i ⟶ i₀),
      let x := markL (IsLocalRing.closedPoint s.residueField)
      let U := normalComponentOpen ((etaleCurveCone X B hX s p).π.app i x)
      (etaleCurveCone X B hX s p).π.app i ⁻¹ᵁ U = normalComponentOpen x ∧
      ∃ (σi τi : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶
          (etaleCurveDiagram X s p).obj i),
        σi ≫ (etaleCurveDiagram X s p).map e =
          (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map e ≫ σ₀ ∧
        τi ≫ (etaleCurveDiagram X s p).map e =
          (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map e ≫ τ₀ ∧
        σi ≫ (etaleCurveStructure X s p).app i = 𝟙 _ ∧
        τi ≫ (etaleCurveStructure X s p).app i = 𝟙 _ ∧
        etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i) ≫ σi =
          etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i) ≫ τi ∧
        σi ((etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i))
          (IsLocalRing.closedPoint s.residueField)) ∈ U ∧
        ∃ (a : Over i),
          let U' := (etaleCurveDiagram X s p).map a.hom ⁻¹ᵁ U
          IsClopen (U' : Set ((etaleCurveDiagram X s p).obj a.left)) ∧
          IsClosedImmersion U'.ι ∧
          (etaleCurveCone X B hX s p).π.app a.left ⁻¹ᵁ U' = normalComponentOpen x ∧
          ∃ (σU τU : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj a.left ⟶
              U'.toScheme),
            σU ≫ U'.ι ≫ (etaleCurveDiagram X s p).map a.hom =
              (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom ≫ σi ∧
            τU ≫ U'.ι ≫ (etaleCurveDiagram X s p).map a.hom =
              (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom ≫ τi ∧
            σU ≫ (U'.ι ≫ (etaleCurveStructure X s p).app a.left) = 𝟙 _ ∧
            τU ≫ (U'.ι ≫ (etaleCurveStructure X s p).app a.left) = 𝟙 _ ∧
            etaleNeighborhoodMark X s.hom
                ((smallEtaleNeighborhoodInclusion X s).obj a.left) ≫ σU =
              etaleNeighborhoodMark X s.hom
                ((smallEtaleNeighborhoodInclusion X s).obj a.left) ≫ τU ∧
            let F := (etaleCurveDiagram X s p).map (a.hom ≫ e)
            let b := (smallEtaleNeighborhoodToSmooth X s).map (a.hom ≫ e)
            let A' := (smallEtaleNeighborhoodToSmooth X s).obj a.left
            let j₁ := pullback.fst F j₀
            let V := pullback U'.ι j₁
            let jV := pullback.fst U'.ι j₁
            IsAffine V ∧ IsOpenImmersion jV ∧
            SmoothOfRelativeDimension 1
              (jV ≫ U'.ι ≫ (etaleCurveStructure X s p).app a.left) ∧
            ∃ (σV τV : A'.left ⟶ V) (r : V ⟶ pullback A'.hom T.hom),
              σV ≫ jV = σU ∧ τV ≫ jV = τU ∧
              r ≫ pullback.fst A'.hom T.hom =
                jV ≫ U'.ι ≫ (etaleCurveStructure X s p).app a.left ∧
              r ≫ pullback.snd A'.hom T.hom =
                pullback.snd U'.ι j₁ ≫ pullback.snd F j₀ ≫ t₀ ∧
              (b ≫ (h₀ ≫ f)).left = σV ≫ r ≫ pullback.snd A'.hom T.hom ∧
              (b ≫ (h₀ ≫ g)).left = τV ≫ r ≫ pullback.snd A'.hom T.hom := by
  intro hσ hτ σ₀ τ₀ j₀ t₀ h₀
  let A₀ := (smallEtaleNeighborhoodToSmooth X s).obj i₀
  let q₀ := (etaleCurveStructure X s p).app i₀
  let Y₀ := etaleCurveOriginalRetainedStage X s p j i₀
  let u₀ := pullback.snd ((smallEtaleNeighborhoodOver X s).obj i₀).hom (j ≫ p)
  let σY₀ := etaleCurveOriginalRetainedSectionStage X s p j σY hσY i₀
  let τY₀ := etaleCurveOriginalRetainedSectionStage X s p j τY hτY i₀
  have hsWhole : σY₀ ≫ j₀ = σ₀ :=
    etaleCurveOriginalRetainedSectionStage_whole X s p j σY hσY i₀
  have htWhole : τY₀ ≫ j₀ = τ₀ :=
    etaleCurveOriginalRetainedSectionStage_whole X s p j τY hτY i₀
  have hsQ : σ₀ ≫ q₀ = 𝟙 _ :=
    etaleCurveOriginalSectionStage_projection X s p (σY ≫ j) hσ i₀
  have htQ : τ₀ ≫ q₀ = 𝟙 _ :=
    etaleCurveOriginalSectionStage_projection X s p (τY ≫ j) hτ i₀
  have hmark₀ := etaleCurveOriginalSectionStages_same_marking
    X s p (σY ≫ j) hσ (τY ≫ j) hτ hmark i₀
  have hp₀ := etaleCurveOriginalRetainedStageMap_isPullback X s p j i₀
  let : IsOpenImmersion j₀ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hp₀.flip inferInstance
  let ABase : Scheme.{u} := ((smallEtaleNeighborhoodOver X s).obj i₀).left
  let gBase : ABase ⟶ X.left := ((smallEtaleNeighborhoodOver X s).obj i₀).hom
  have hAffBase : IsAffine ABase :=
    inferInstanceAs (IsAffine ((smallEtaleNeighborhoodToSmooth X s).obj i₀).left)
  let hBaseAffine : IsAffineHom gBase :=
    @isAffineHom_of_isAffine _ _ gBase hAffBase inferInstance
  let hProjAffine : IsAffineHom u₀ :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback gBase (j ≫ p)) hBaseAffine
  let : IsAffine Y₀ := isAffine_of_isAffineHom u₀
  have hj₀q : j₀ ≫ q₀ = pullback.fst gBase (j ≫ p) := pullback.lift_fst _ _ _
  let hSmooth₀ : SmoothOfRelativeDimension 1 (j₀ ≫ q₀) := by
    rw [hj₀q]
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
      (IsPullback.of_hasPullback gBase (j ≫ p)).flip hSmooth
  have hBaseOver : gBase ≫ X.hom = A₀.hom := h₀.w
  have hCondition : u₀ ≫ (j ≫ p) = pullback.fst gBase (j ≫ p) ≫ gBase :=
    (pullback.condition (f := gBase) (g := j ≫ p)).symm
  have hw₀ : t₀ ≫ T.hom = j₀ ≫ q₀ ≫ A₀.hom := by
    calc
      _ = u₀ ≫ (t ≫ T.hom) := Category.assoc _ _ _
      _ = u₀ ≫ (j ≫ p ≫ X.hom) := congrArg (fun z : Y ⟶ S => u₀ ≫ z) ht
      _ = (u₀ ≫ (j ≫ p)) ≫ X.hom := (Category.assoc _ _ _).symm
      _ = (pullback.fst gBase (j ≫ p) ≫ gBase) ≫ X.hom :=
        congrArg (fun z : Y₀ ⟶ X.left => z ≫ X.hom) hCondition
      _ = pullback.fst gBase (j ≫ p) ≫ A₀.hom :=
        (Category.assoc _ _ _).trans
          (congrArg (fun z : ABase ⟶ S => pullback.fst gBase (j ≫ p) ≫ z) hBaseOver)
      _ = _ := (congrArg (fun z : Y₀ ⟶ A₀.left => z ≫ A₀.hom) hj₀q).symm.trans
        (Category.assoc _ _ _)
  have hf₀ : (h₀ ≫ f).left = σY₀ ≫ t₀ := by
    change h₀.left ≫ f.left = _
    exact (congrArg (fun z => h₀.left ≫ z) hf).trans
      (etaleCurveOriginalRetainedSectionStage_target X s p j σY hσY i₀ t).symm
  have hg₀ : (h₀ ≫ g).left = τY₀ ≫ t₀ := by
    change h₀.left ≫ g.left = _
    exact (congrArg (fun z => h₀.left ≫ z) hg).trans
      (etaleCurveOriginalRetainedSectionStage_target X s p j τY hτY i₀ t).symm
  obtain ⟨markL, hmarkLq, hmarkLπ, i, e, hpre, σi, τi,
    hsF, htF, hsq, htq, hmarki, hmem,
    a, hclopen, hclosed, hpre', σU, τU, hsF', htF', hsq', htq', hmark'⟩ :=
    exists_etaleCurve_fixed_clopen_section_pair X s p B hX i₀ σ₀ τ₀ hsQ htQ hmark₀
  let x := markL (IsLocalRing.closedPoint s.residueField)
  let U := normalComponentOpen ((etaleCurveCone X B hX s p).π.app i x)
  let U' := (etaleCurveDiagram X s p).map a.hom ⁻¹ᵁ U
  let := hclosed
  have hfinal := exists_etaleCurve_fixedClopen_retained_target_pair
    (hSmoothOriginal := hSmooth₀) X s p e a U' j₀
    σ₀ τ₀ σY₀ τY₀ hsWhole htWhole σi τi hsF htF
    σU τU hsF' htF' t₀ hw₀ (h₀ ≫ f) (h₀ ≫ g) hf₀ hg₀
  exact ⟨markL, hmarkLq, hmarkLπ, i, e, hpre, σi, τi,
    hsF, htF, hsq, htq, hmarki, hmem,
    a, hclopen, hclosed, hpre', σU, τU, hsF', htF', hsq', htq', hmark', hfinal⟩

end AlgebraicGeometry.Scheme.SmoothSite
