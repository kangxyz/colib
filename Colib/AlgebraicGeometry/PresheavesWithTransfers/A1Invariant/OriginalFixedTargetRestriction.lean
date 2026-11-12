/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenFixedMarking
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.OriginalFixedTargetGeometry
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodRestrictionTwoStage
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.EtaleStageOpenFixedTargetRestriction

/-! # Actual original fixed geometry consumed by the same-root restriction theorem

All geometry is obtained once. The final restriction is expressed on an original
marked neighborhood, with the original two target maps, not substituted maps.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u v
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Apply the actual same-root restriction consumer to the single selected
fixed geometry, then recover the original neighborhood maps exactly. -/
theorem exists_original_fixed_target_restriction
    {K : Type u} [Field K] (P : PresheafWithTransfers.{v} K)
    (hP : PresheafWithTransfers.IsA1Invariant P)
    (X : SmoothSite (Spec (.of K))) [IsAffine X.left]
    (s : GeometricPoint X.left) {C Y : Scheme.{u}} (p : C ⟶ X.left)
    [IsNormal X.left] [IsLocallyNoetherian X.left] [IsNormal C] [IsProper p]
    (j : Y ⟶ C) [IsAffine Y] [IsOpenImmersion j]
    [hSmooth : SmoothOfRelativeDimension 1 (j ≫ p)]
    {Z : Scheme.{u}} (d : Z ⟶ C) [IsClosedImmersion d] [IsFinite (d ≫ p)]
    (hd : Set.range d = (Set.range j)ᶜ)
    (σY τY : X.left ⟶ Y)
    (hσY : σY ≫ (j ≫ p) = 𝟙 X.left) (hτY : τY ≫ (j ≫ p) = 𝟙 X.left)
    (hmark : s.hom ≫ (σY ≫ j) = s.hom ≫ (τY ≫ j))
    {T : SmoothSite (Spec (.of K))} (t : Y ⟶ T.left)
    (ht : t ≫ T.hom = j ≫ p ≫ X.hom)
    (f g : X ⟶ T) (hf : f.left = σY ≫ t) (hg : g.left = τY ≫ t)
    {Nchart YN E : Scheme.{u}} [IrreducibleSpace Nchart]
    {A : Type u} [CommRing A] (v : C ⟶ Nchart) [Flat v]
    (q : Nchart ⟶ Spec (.of A)) (bOriginal : X.left ⟶ Spec (.of A))
    (hCartesian : IsPullback v p q bOriginal)
    (jN : YN ⟶ Nchart) (y : Y ⟶ YN) (hY : IsPullback j y v jN)
    (π : Nchart ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = q)
    (aY : YN ⟶ Spec (.of (Polynomial A)))
    (haY : aY ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = jN ≫ q)
    (hjN : jN ≫ π = aY ≫ projectiveLineXChart A)
    (eChart : E ⟶ Nchart) [IsOpenImmersion eChart] [Nonempty E]
    (aE : E ⟶ Spec (.of (Polynomial A))) [Etale aE]
    (haE : aE ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = eChart ≫ q)
    (heChart : eChart ≫ π = aE ≫ projectiveLineXChart A)
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    (i₀ : SmallEtaleNeighborhood X s)
    (hp : IsProjectiveMorphism p) (k : ℕ)
    (hn : ∀ (A : SmoothSite (Spec (.of K)))
      (z : PresheafWithTransfers.sections P ((Cor.graphFunctor K).obj A)), (k + 1) • z = 0)
    (hnUnit : IsUnit ((k + 1 : ℕ) : ↥(etaleLocalRing B X.left hX s))) :
    ∃ Anew : EtaleNeighborhood X s.hom,
      ((PresheafWithTransfers.toPresheaf K).obj P).map
          (etaleNeighborhoodHom X s.hom Anew ≫ f).op =
        ((PresheafWithTransfers.toPresheaf K).obj P).map
          (etaleNeighborhoodHom X s.hom Anew ≫ g).op := by
  obtain ⟨markL, hmarkLq, hmarkLπ, i, e, hpre, σi, τi,
    hsF, htF, hsq, htq, hmarki, hmem,
    a, hclopen, hclosed, hpre', σU, τU, hsF', htF', hsq', htq', hmark',
    hAff, hOpen, hRel, σV, τV, r, hsV, htV, hr₁, hr₂, hfFinal, hgFinal,
    hdClosed, hdFinite, hdComplement, hsRange, htRange, hsAvoid, htAvoid, hFlat,
    φ, hφ, hpb, hπFinite, hπStructure, cV, cE, hcV, hcVMap, hjπ, hCE,
    hcE, hcEMap, he⟩ :=
    exists_original_fixed_target_geometry (hSmooth := hSmooth)
      X s p j d hd σY τY hσY hτY hmark t ht f g hf hg
      v q bOriginal hCartesian jN y hY π hπ aY haY hjN eChart aE haE heChart B hX i₀
  let : IsLocallyNoetherian ((etaleCurveDiagram X s p).obj i) :=
    (etaleCurveDiagram_isNoetherian X s p i).toIsLocallyNoetherian
  let x := markL (IsLocalRing.closedPoint s.residueField)
  let U := normalComponentOpen ((etaleCurveCone X B hX s p).π.app i x)
  let U' := (etaleCurveDiagram X s p).map a.hom ⁻¹ᵁ U
  let F := (etaleCurveDiagram X s p).map (a.hom ≫ e)
  let j₀ := etaleCurveOriginalRetainedStageMap X s p j i₀
  let d₀ := etaleBoundaryBaseChangeMap ((smallEtaleNeighborhoodOver X s).obj i₀).hom p d
  let jV := pullback.fst U'.ι (pullback.fst F j₀)
  let dFinal := pullback.fst U'.ι (pullback.fst F d₀)
  let qStage := (etaleCurveStructure X s p).app a.left
  let qU := U'.ι ≫ qStage
  let vStage := pullback.snd ((smallEtaleNeighborhoodOver X s).obj a.left).hom p ≫ v
  let πU := U'.ι ≫ projectiveLineCoverOfActualCartesian q φ vStage qStage hpb π hπ
  let bSmall := (smallEtaleNeighborhoodToSmooth X s).map (a.hom ≫ e)
  let h₀ := etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i₀)
  let : IsClosedImmersion U'.ι := hclosed
  let : IsAffine (pullback U'.ι (pullback.fst F j₀)) := hAff
  let : IsOpenImmersion jV := hOpen
  let : SmoothOfRelativeDimension 1 (jV ≫ qU) := hRel
  let : IsClosedImmersion dFinal := hdClosed
  let : IsFinite (dFinal ≫ qU) := hdFinite
  let : Flat (U'.ι ≫ vStage) := hFlat
  let : Etale cE := hCE
  let : IsFinite πU := hπFinite
  have hqStage : IsProper qStage :=
    inferInstanceAs (IsProper (pullback.fst ((smallEtaleNeighborhoodOver X s).obj a.left).hom p))
  have hUProper : IsProper U'.ι := inferInstance
  let : IsProper qU :=
    MorphismProperty.comp_mem (@IsProper) U'.ι qStage hUProper hqStage
  let : IsClosedImmersion (σU ≫ qU) :=
    (congrArg IsClosedImmersion hsq').mpr inferInstance
  let : IsClosedImmersion (τU ≫ qU) :=
    (congrArg IsClosedImmersion htq').mpr inferInstance
  let : IsClosedImmersion σU := IsClosedImmersion.of_comp σU qU
  let : IsClosedImmersion τU := IsClosedImmersion.of_comp τU qU
  let a₀ : Over a.left := Over.mk (𝟙 a.left)
  have hmark₀ := etaleStageOpenSection_same_marking_of_fixed
    X s p a.left U' σU τU hsq' htq' hmark' a₀
  obtain ⟨ℓ, Anew, w, hEq⟩ := exists_etaleStageOpen_fixed_target_restriction
    P hP X s p a.left U' dFinal B hX σU τU hsq' htq'
    jV hsRange htRange hsAvoid htAvoid a₀ hmark₀
    πU hπStructure cV hcV hjπ (U'.ι ≫ vStage) eChart cE hcE he hdComplement
    σV τV hsV htV r hr₁ (bSmall ≫ (h₀ ≫ f)) (bSmall ≫ (h₀ ≫ g)) hfFinal hgFinal
    k hn x hpre' hp hnUnit
  exact ⟨Anew, etaleNeighborhood_restriction_maps_eq_of_two_small_stages
    X T s e a ℓ Anew w ((PresheafWithTransfers.toPresheaf K).obj P) f g hEq⟩

end AlgebraicGeometry.Scheme.SmoothSite
