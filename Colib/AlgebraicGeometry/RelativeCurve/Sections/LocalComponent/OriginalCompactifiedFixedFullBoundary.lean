/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.OriginalCompactifiedFixedRetainedTarget
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.FixedClopenFullBoundary

/-! # Full original boundary on the same selected fixed clopen

The boundary and retained source use the identical two literal pullbacks.
There is no second component selection and no reduction of the boundary.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

private theorem originalBoundary_range_of_isPullback {P X Y S : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hp : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
  rw [← hp.isoPullback_hom_fst]
  change Set.range (pullback.fst f g ∘ hp.isoPullback.hom) = _
  rw [Set.range_comp, hp.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]

/-- On any already selected two-step small refinement and final clopen, the full
original boundary remains closed, finite over the same base, and the exact
complement of the retained source constructed by FixedClopenRetainedTarget. -/
theorem originalCompactified_fixedClopen_fullBoundary
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N Y Z : Scheme.{u}} (p : N ⟶ X.left)
    (j : Y ⟶ N) (d : Z ⟶ N) [IsClosedImmersion d] [IsFinite (d ≫ p)]
    (hd : Set.range d = (Set.range j)ᶜ)
    {i₀ i : SmallEtaleNeighborhood X s} (e : i ⟶ i₀) (a : Over i)
    (U : ((etaleCurveDiagram X s p).obj a.left).Opens) [IsClosedImmersion U.ι] :
    let d₀ := etaleBoundaryBaseChangeMap ((smallEtaleNeighborhoodOver X s).obj i₀).hom p d
    let j₀ := etaleCurveOriginalRetainedStageMap X s p j i₀
    let F := (etaleCurveDiagram X s p).map (a.hom ≫ e)
    let dFinal := pullback.fst U.ι (pullback.fst F d₀)
    IsClosedImmersion dFinal ∧
      IsFinite (dFinal ≫ U.ι ≫ (etaleCurveStructure X s p).app a.left) ∧
      Set.range dFinal = (Set.range (pullback.fst U.ι (pullback.fst F j₀)))ᶜ := by
  intro d₀ j₀ F dFinal
  let g₀ := ((smallEtaleNeighborhoodOver X s).obj i₀).hom
  let q₀ := (etaleCurveStructure X s p).app i₀
  let hclosed₀ : IsClosedImmersion d₀ :=
    etaleBoundaryBaseChangeMap_isClosedImmersion g₀ p d
  let hfinite₀ : IsFinite (d₀ ≫ q₀) := by
    change IsFinite (etaleBoundaryBaseChangeMap g₀ p d ≫ pullback.fst g₀ p)
    rw [etaleBoundaryBaseChangeMap_fst]
    infer_instance
  have hd₀ : Set.range d₀ = (Set.range j₀)ᶜ := by
    change Set.range (etaleBoundaryBaseChangeMap g₀ p d) =
      (Set.range (etaleCurveOriginalRetainedStageMap X s p j i₀))ᶜ
    rw [originalBoundary_range_of_isPullback (etaleBoundaryBaseChangeMap_isPullback g₀ p d),
      originalBoundary_range_of_isPullback
        (etaleCurveOriginalRetainedStageMap_isPullback X s p j i₀), hd]
    rfl
  have hclosed₁ : IsClosedImmersion (pullback.fst F d₀) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (IsPullback.of_hasPullback F d₀).flip hclosed₀
  have hclosedFinal : IsClosedImmersion dFinal :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (IsPullback.of_hasPullback U.ι (pullback.fst F d₀)).flip hclosed₁
  exact ⟨hclosedFinal,
    @fixedClopen_fullBoundary_finite _ _ _ _ _ _
      F ((etaleCurveStructure X s p).app a.left) q₀
      ((smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map (a.hom ≫ e))
      (etaleCurveDiagram_isPullback X s p (a.hom ≫ e)) U.ι
      (inferInstance : IsClosedImmersion U.ι) d₀ hfinite₀,
    fixedClopen_fullBoundary_complement F U.ι j₀ d₀ hd₀⟩

/-- The final literal retained source is Cartesian over the original retained
inclusion. Both projections are the original native pullback projections. -/
theorem originalCompactified_fixedClopen_retained_isPullback
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N Y : Scheme.{u}} (p : N ⟶ X.left) (j : Y ⟶ N)
    {i₀ i : SmallEtaleNeighborhood X s} (e : i ⟶ i₀) (a : Over i)
    (U : ((etaleCurveDiagram X s p).obj a.left).Opens) :
    let F := (etaleCurveDiagram X s p).map (a.hom ≫ e)
    let j₀ := etaleCurveOriginalRetainedStageMap X s p j i₀
    IsPullback (pullback.fst U.ι (pullback.fst F j₀))
      (pullback.snd U.ι (pullback.fst F j₀) ≫ pullback.snd F j₀ ≫
        pullback.snd ((smallEtaleNeighborhoodOver X s).obj i₀).hom (j ≫ p))
      (U.ι ≫ F ≫ pullback.snd ((smallEtaleNeighborhoodOver X s).obj i₀).hom p) j := by
  intro F j₀
  have hp := ((IsPullback.of_hasPullback U.ι (pullback.fst F j₀)).paste_vert
    (IsPullback.of_hasPullback F j₀)).paste_vert
      (etaleCurveOriginalRetainedStageMap_isPullback X s p j i₀)
  let v₂ := pullback.snd U.ι (pullback.fst F j₀)
  let v₁ := pullback.snd F j₀
  let v₀ := pullback.snd ((smallEtaleNeighborhoodOver X s).obj i₀).hom (j ≫ p)
  let r₀ := pullback.snd ((smallEtaleNeighborhoodOver X s).obj i₀).hom p
  have hleft : (v₂ ≫ v₁) ≫ v₀ = v₂ ≫ v₁ ≫ v₀ := Category.assoc v₂ v₁ v₀
  have hright : (U.ι ≫ F) ≫ r₀ = U.ι ≫ F ≫ r₀ := Category.assoc U.ι F r₀
  exact (congrArg₂
    (fun (l : pullback U.ι (pullback.fst F j₀) ⟶ Y) (r : U.toScheme ⟶ N) =>
      IsPullback (pullback.fst U.ι (pullback.fst F j₀)) l r j) hleft hright).mp hp

/-- Append the full boundary to precisely the witnesses selected by the original
fixed-retained-target theorem. No geometric choices are repeated. -/
theorem exists_original_compactified_fixed_retained_target_fullBoundary
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S) [IsAffine X.left]
    (s : GeometricPoint X.left) {N Y : Scheme.{u}} (p : N ⟶ X.left)
    [IsNormal X.left] [IsLocallyNoetherian X.left] [IsNormal N] [IsProper p]
    (j : Y ⟶ N) [IsAffine Y] [IsOpenImmersion j]
    [hSmooth : SmoothOfRelativeDimension 1 (j ≫ p)]
    {Z : Scheme.{u}} (d : Z ⟶ N) [IsClosedImmersion d] [IsFinite (d ≫ p)]
    (hd : Set.range d = (Set.range j)ᶜ)
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
    let d₀ := etaleBoundaryBaseChangeMap ((smallEtaleNeighborhoodOver X s).obj i₀).hom p d
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
              (b ≫ (h₀ ≫ g)).left = τV ≫ r ≫ pullback.snd A'.hom T.hom ∧
              IsClosedImmersion (pullback.fst U'.ι (pullback.fst F d₀)) ∧
              IsFinite (pullback.fst U'.ι (pullback.fst F d₀) ≫ U'.ι ≫
                (etaleCurveStructure X s p).app a.left) ∧
              Set.range (pullback.fst U'.ι (pullback.fst F d₀)) = (Set.range jV)ᶜ := by
  intro hσ hτ σ₀ τ₀ j₀ t₀ h₀ d₀
  obtain ⟨markL, hmarkLq, hmarkLπ, i, e, hpre, σi, τi,
    hsF, htF, hsq, htq, hmarki, hmem,
    a, hclopen, hclosed, hpre', σU, τU, hsF', htF', hsq', htq', hmark',
    hAff, hOpen, hRel, σV, τV, r, hsV, htV, hr₁, hr₂, hfFinal, hgFinal⟩ :=
    exists_original_compactified_fixed_retained_target (hSmooth := hSmooth)
      X s p j σY τY hσY hτY
      hmark t ht f g hf hg B hX i₀
  let x := markL (IsLocalRing.closedPoint s.residueField)
  let U := normalComponentOpen ((etaleCurveCone X B hX s p).π.app i x)
  let U' := (etaleCurveDiagram X s p).map a.hom ⁻¹ᵁ U
  let := hclosed
  have hBoundary := originalCompactified_fixedClopen_fullBoundary X s p j d hd e a U'
  exact ⟨markL, hmarkLq, hmarkLπ, i, e, hpre, σi, τi,
    hsF, htF, hsq, htq, hmarki, hmem,
    a, hclopen, hclosed, hpre', σU, τU, hsF', htF', hsq', htq', hmark',
    hAff, hOpen, hRel, σV, τV, r, hsV, htV, hr₁, hr₂, hfFinal, hgFinal, hBoundary⟩

end AlgebraicGeometry.Scheme.SmoothSite
