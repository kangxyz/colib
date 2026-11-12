/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenSections

/-! # The unchanged marking on actual restarted component stages -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- A common fixed marking gives the common marking on every actual restarted
stage, by its two actual Cartesian projections, including the identity index. -/
theorem etaleStageOpenSection_same_marking_of_fixed
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hτ : τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hmark : etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i) ≫ σ =
      etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i) ≫ τ)
    (a : Over i) :
    etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj a.left) ≫
        etaleStageOpenSection X s p i U σ hσ a =
      etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj a.left) ≫
        etaleStageOpenSection X s p i U τ hτ a := by
  let μ := etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj a.left)
  let ξ := etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i)
  let b := (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom
  let σa := etaleStageOpenSection X s p i U σ hσ a
  let τa := etaleStageOpenSection X s p i U τ hτ a
  let pr := pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι
  let qa := (etaleStageOpenStructure X s p i U).app a
  have hμ : μ ≫ b = ξ :=
    etaleNeighborhoodMark_map X s.hom ((smallEtaleNeighborhoodInclusion X s).map a.hom)
  have hs : (μ ≫ σa) ≫ pr = ξ ≫ σ :=
    (Category.assoc μ σa pr).trans
      ((congrArg (fun z => μ ≫ z) (etaleStageOpenSection_snd X s p i U σ hσ a)).trans
      ((Category.assoc μ b σ).symm.trans (congrArg (fun z => z ≫ σ) hμ)))
  have ht : (μ ≫ τa) ≫ pr = ξ ≫ τ :=
    (Category.assoc μ τa pr).trans
      ((congrArg (fun z => μ ≫ z) (etaleStageOpenSection_snd X s p i U τ hτ a)).trans
      ((Category.assoc μ b τ).symm.trans (congrArg (fun z => z ≫ τ) hμ)))
  have hsq : (μ ≫ σa) ≫ qa = μ :=
    (Category.assoc μ σa qa).trans
      ((congrArg (fun z => μ ≫ z) (etaleStageOpenSection_structure X s p i U σ hσ a)).trans
        (Category.comp_id μ))
  have htq : (μ ≫ τa) ≫ qa = μ :=
    (Category.assoc μ τa qa).trans
      ((congrArg (fun z => μ ≫ z) (etaleStageOpenSection_structure X s p i U τ hτ a)).trans
        (Category.comp_id μ))
  exact (etaleStageOpenStructure_isPullback X s p i U a).hom_ext
    (hs.trans (hmark.trans ht.symm)) (hsq.trans htq.symm)

end AlgebraicGeometry.Scheme.SmoothSite
