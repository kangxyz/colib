/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleCurveMarkedComponentSelection

/-! # From the original common marking to both sections on one fixed small clopen

The component selection and the connected intermediate-base factorization are
composed in their original order. Both index arrows and all whole-map recovery
equations are retained. No component-membership or limit-preimage certificate
is an input, and no integrality is asserted for the final small-stage base.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Select the original marked strict-local component, descend it, and then
factor both whole sections through its actual small-stage clopen pullback. -/
theorem exists_etaleCurve_fixed_clopen_section_pair
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    [IsNormal X.left] [IsLocallyNoetherian X.left] [IsNormal N] [IsProper p]
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    (i₀ : SmallEtaleNeighborhood X s)
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i₀ ⟶
      (etaleCurveDiagram X s p).obj i₀)
    (hσ : σ ≫ (etaleCurveStructure X s p).app i₀ = 𝟙 _)
    (hτ : τ ≫ (etaleCurveStructure X s p).app i₀ = 𝟙 _)
    (hmark : etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj i₀) ≫ σ =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj i₀) ≫ τ) :
    ∃ (markL : Spec (.of s.residueField) ⟶ (etaleCurveCone X B hX s p).pt),
      markL ≫ pullback.fst (strictHenselizationToBase B X.left hX s) p =
        geometricPointToStrictHenselization B X.left hX s ∧
      markL ≫ (etaleCurveCone X B hX s p).π.app i₀ =
        etaleNeighborhoodMark X s.hom
          ((smallEtaleNeighborhoodInclusion X s).obj i₀) ≫ σ ∧
      ∃ (i : SmallEtaleNeighborhood X s) (e : i ⟶ i₀),
      let x := markL (IsLocalRing.closedPoint s.residueField)
      let U := normalComponentOpen ((etaleCurveCone X B hX s p).π.app i x)
      (etaleCurveCone X B hX s p).π.app i ⁻¹ᵁ U = normalComponentOpen x ∧
      ∃ (σi τi : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶
          (etaleCurveDiagram X s p).obj i),
        σi ≫ (etaleCurveDiagram X s p).map e =
          (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map e ≫ σ ∧
        τi ≫ (etaleCurveDiagram X s p).map e =
          (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map e ≫ τ ∧
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
                ((smallEtaleNeighborhoodInclusion X s).obj a.left) ≫ τU := by
  obtain ⟨markL, hmarkLq, hmarkLπ, i, e, hpre, σi, τi,
      hsF, htF, hsq, htq, hmarki, hmem⟩ :=
    exists_etaleCurve_marked_component_section_stage X s p B hX i₀ σ τ hσ hτ hmark
  let x := markL (IsLocalRing.closedPoint s.residueField)
  let U := normalComponentOpen ((etaleCurveCone X B hX s p).π.app i x)
  obtain ⟨a, hclopen, hclosed, hpre', σU, τU, hsF', htF', hsq', htq', hmark'⟩ :=
    exists_small_fixed_clopen_section_pair X s p B hX i U
      (isClopen_normalComponentOpen _) x hpre σi τi hsq htq hmarki hmem
  exact ⟨markL, hmarkLq, hmarkLπ, i, e, hpre, σi, τi,
    hsF, htF, hsq, htq, hmarki, hmem,
    a, hclopen, hclosed, hpre', σU, τU, hsF', htF', hsq', htq', hmark'⟩

end AlgebraicGeometry.Scheme.SmoothSite
