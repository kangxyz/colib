/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.OriginalFixedCoverAndCharts

/-! # All actual fixed-target geometry with one set of chosen witnesses

Obtain the original full-boundary construction once and attach its finite cover
and two distinct coordinates without choosing another clopen, section or target.
The final small index is a.left. All original recovery equations are retained.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The complete original fixed geometry, ready for the fixed-target restriction
consumer. No producer of stage families or boundary compatibilities is assumed. -/
theorem exists_original_fixed_target_geometry
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S) [IsAffine X.left]
    (s : GeometricPoint X.left) {C Y : Scheme.{u}} (p : C ⟶ X.left)
    [IsNormal X.left] [IsLocallyNoetherian X.left] [IsNormal C] [IsProper p]
    (j : Y ⟶ C) [IsAffine Y] [IsOpenImmersion j]
    [hSmooth : SmoothOfRelativeDimension 1 (j ≫ p)]
    {Z : Scheme.{u}} (d : Z ⟶ C) [IsClosedImmersion d] [IsFinite (d ≫ p)]
    (hd : Set.range d = (Set.range j)ᶜ)
    (σY τY : X.left ⟶ Y)
    (hσY : σY ≫ (j ≫ p) = 𝟙 X.left) (hτY : τY ≫ (j ≫ p) = 𝟙 X.left)
    (hmark : s.hom ≫ (σY ≫ j) = s.hom ≫ (τY ≫ j))
    {T : SmoothSite S} (t : Y ⟶ T.left)
    (ht : t ≫ T.hom = j ≫ p ≫ X.hom)
    (f g : X ⟶ T) (hf : f.left = σY ≫ t) (hg : g.left = τY ≫ t)
    {Nchart YN E : Scheme.{u}}
    {A : Type u} [CommRing A] (v : C ⟶ Nchart) [Flat v]
    (q : Nchart ⟶ Spec (.of A)) (bOriginal : X.left ⟶ Spec (.of A))
    (hCartesian : IsPullback v p q bOriginal)
    (jN : YN ⟶ Nchart) (y : Y ⟶ YN) (hY : IsPullback j y v jN)
    (π : Nchart ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = q)
    (aY : YN ⟶ Spec (.of (Polynomial A)))
    (haY : aY ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = jN ≫ q)
    (hjN : jN ≫ π = aY ≫ projectiveLineXChart A)
    (eChart : E ⟶ Nchart)
    (aE : E ⟶ Spec (.of (Polynomial A))) [Etale aE]
    (haE : aE ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = eChart ≫ q)
    (heChart : eChart ≫ π = aE ≫ projectiveLineXChart A)
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
              Set.range (pullback.fst U'.ι (pullback.fst F d₀)) = (Set.range jV)ᶜ ∧
              Set.range σU ⊆ Set.range jV ∧ Set.range τU ⊆ Set.range jV ∧
              (∀ z, pullback.fst U'.ι (pullback.fst F d₀) z ∉ Set.range σU) ∧
              (∀ z, pullback.fst U'.ι (pullback.fst F d₀) z ∉ Set.range τU) ∧
              let R := ((smallEtaleNeighborhoodInclusion X s).obj a.left).obj.left.unop
              let vStage := pullback.snd ((smallEtaleNeighborhoodOver X s).obj a.left).hom p ≫ v
              let qStage := (etaleCurveStructure X s p).app a.left
              let vY := pullback.snd U'.ι j₁ ≫ pullback.snd F j₀ ≫
                pullback.snd ((smallEtaleNeighborhoodOver X s).obj i₀).hom (j ≫ p)
              Flat (U'.ι ≫ vStage) ∧
              ∃ (φ : A →+* R)
                (_hφ : Spec.map (CommRingCat.ofHom φ) =
                  ((smallEtaleNeighborhoodOver X s).obj a.left).hom ≫ bOriginal)
                (hpb : IsPullback vStage qStage q (Spec.map (CommRingCat.ofHom φ))),
                let πU := U'.ι ≫ projectiveLineCoverOfActualCartesian q φ vStage qStage hpb π hπ
                IsFinite πU ∧ πU ≫ (projectiveLine R ↘ Spec (.of R)) = U'.ι ≫ qStage ∧
                ∃ (cV : V ⟶ Spec (.of (Polynomial R)))
                  (cE : pullback (U'.ι ≫ vStage) eChart ⟶ Spec (.of (Polynomial R))),
                  cV ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
                    jV ≫ (U'.ι ≫ qStage) ∧
                  cV ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ)) =
                    (vY ≫ y) ≫ aY ∧
                  jV ≫ πU = cV ≫ projectiveLineXChart R ∧ Etale cE ∧
                  cE ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
                    pullback.fst (U'.ι ≫ vStage) eChart ≫ (U'.ι ≫ qStage) ∧
                  cE ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ)) =
                    pullback.snd (U'.ι ≫ vStage) eChart ≫ aE ∧
                  pullback.fst (U'.ι ≫ vStage) eChart ≫ πU = cE ≫ projectiveLineXChart R := by
  intro hσ hτ σ₀ τ₀ j₀ t₀ h₀ d₀
  obtain ⟨markL, hmarkLq, hmarkLπ, i, e, hpre, σi, τi,
    hsF, htF, hsq, htq, hmarki, hmem,
    a, hclopen, hclosed, hpre', σU, τU, hsF', htF', hsq', htq', hmark',
    hAff, hOpen, hRel, σV, τV, r, hsV, htV, hr₁, hr₂, hfFinal, hgFinal,
    hdClosed, hdFinite, hdComplement⟩ :=
    exists_original_compactified_fixed_retained_target_fullBoundary (hSmooth := hSmooth)
      X s p j d hd σY τY hσY hτY hmark t ht f g hf hg B hX i₀
  let x := markL (IsLocalRing.closedPoint s.residueField)
  let U := normalComponentOpen ((etaleCurveCone X B hX s p).π.app i x)
  let U' := (etaleCurveDiagram X s p).map a.hom ⁻¹ᵁ U
  let F := (etaleCurveDiagram X s p).map (a.hom ≫ e)
  let jV := pullback.fst U'.ι (pullback.fst F j₀)
  let dFinal := pullback.fst U'.ι (pullback.fst F d₀)
  let := hclosed
  have hsRange : Set.range σU ⊆ Set.range jV := by
    rintro z ⟨w, rfl⟩
    exact ⟨σV w, congrArg (fun z => z w) hsV⟩
  have htRange : Set.range τU ⊆ Set.range jV := by
    rintro z ⟨w, rfl⟩
    exact ⟨τV w, congrArg (fun z => z w) htV⟩
  have hsAvoid : ∀ z, dFinal z ∉ Set.range σU := by
    intro z hz
    have hmem : dFinal z ∈ Set.range dFinal := Set.mem_range_self z
    rw [hdComplement] at hmem
    exact hmem (hsRange hz)
  have htAvoid : ∀ z, dFinal z ∉ Set.range τU := by
    intro z hz
    have hmem : dFinal z ∈ Set.range dFinal := Set.mem_range_self z
    rw [hdComplement] at hmem
    exact hmem (htRange hz)
  have hUFlat : Flat U'.ι :=
    inferInstanceAs (Flat (((etaleCurveDiagram X s p).obj a.left).ofRestrict
      U'.isOpenEmbedding))
  let gStage := ((smallEtaleNeighborhoodOver X s).obj a.left).hom
  have hgStage : Etale gStage := by
    change Etale (etaleNeighborhoodHom X s.hom
      ((smallEtaleNeighborhoodInclusion X s).obj a.left)).left
    infer_instance
  have hprEtale : Etale (pullback.snd gStage p) :=
    MorphismProperty.of_isPullback (P := @Etale)
      (IsPullback.of_hasPullback gStage p) hgStage
  have hprFlat : Flat (pullback.snd gStage p) :=
    (Etale.iff_flat_and_formallyUnramified.mp hprEtale).1
  have hFlat : Flat (U'.ι ≫ (pullback.snd gStage p ≫ v)) :=
    @Flat.comp _ _ _ U'.ι (pullback.snd gStage p ≫ v) hUFlat
      (@Flat.comp _ _ _ (pullback.snd gStage p) v hprFlat inferInstance)
  have hcharts := exists_original_fixed_cover_and_charts
    X s p v q bOriginal hCartesian j jN y hY π hπ aY haY hjN
    eChart aE haE heChart e a U'
  exact ⟨markL, hmarkLq, hmarkLπ, i, e, hpre, σi, τi,
    hsF, htF, hsq, htq, hmarki, hmem,
    a, hclopen, hclosed, hpre', σU, τU, hsF', htF', hsq', htq', hmark',
    hAff, hOpen, hRel, σV, τV, r, hsV, htV, hr₁, hr₂, hfFinal, hgFinal,
    hdClosed, hdFinite, hdComplement, hsRange, htRange, hsAvoid, htAvoid, hFlat, hcharts⟩

end AlgebraicGeometry.Scheme.SmoothSite
