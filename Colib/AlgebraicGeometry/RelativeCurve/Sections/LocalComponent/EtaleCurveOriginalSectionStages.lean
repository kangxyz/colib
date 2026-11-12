/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleCurveFixedClopenSections
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartCompactifiedSections

/-! # Original sections on every actual small-neighborhood curve

The original base need not itself be a Spec object or an index of the small diagram.
Each section is pulled back directly along the actual original-neighborhood morphism.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [QuasiSeparatedSpace S]
  (X : SmoothSite S) (s : GeometricPoint X.left)
  {N : Scheme.{u}} (p : N ⟶ X.left)
  (σ : X.left ⟶ N)

/-- Pull the original section back to the actual base-first diagram object. -/
def etaleCurveOriginalSectionStage (hσ : σ ≫ p = 𝟙 _) (i : SmallEtaleNeighborhood X s) :
    (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶
      (etaleCurveDiagram X s p).obj i :=
  pullback.lift (𝟙 (((smallEtaleNeighborhoodOver X s).obj i).left))
    (((smallEtaleNeighborhoodOver X s).obj i).hom ≫ σ)
    ((Category.id_comp _).trans
      ((Category.assoc ((smallEtaleNeighborhoodOver X s).obj i).hom σ p).trans
        ((congrArg (fun z : X.left ⟶ X.left =>
          ((smallEtaleNeighborhoodOver X s).obj i).hom ≫ z) hσ).trans
          (Category.comp_id _))).symm)

variable (hσ : σ ≫ p = 𝟙 _)

@[reassoc (attr := simp)]
theorem etaleCurveOriginalSectionStage_projection (i : SmallEtaleNeighborhood X s) :
    etaleCurveOriginalSectionStage X s p σ hσ i ≫
      (etaleCurveStructure X s p).app i = 𝟙 _ := pullback.lift_fst _ _ _

@[reassoc]
theorem etaleCurveOriginalSectionStage_original (i : SmallEtaleNeighborhood X s) :
    etaleCurveOriginalSectionStage X s p σ hσ i ≫
      pullback.snd ((smallEtaleNeighborhoodOver X s).obj i).hom p =
      (etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i)).left ≫ σ :=
  pullback.lift_snd _ _ _

/-- Whole original target maps are preserved, not merely pointwise images. -/
@[reassoc]
theorem etaleCurveOriginalSectionStage_target (i : SmallEtaleNeighborhood X s)
    {T : Scheme.{u}} (t : N ⟶ T) :
    etaleCurveOriginalSectionStage X s p σ hσ i ≫
      (pullback.snd ((smallEtaleNeighborhoodOver X s).obj i).hom p ≫ t) =
      (etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i)).left ≫
        (σ ≫ t) := by
  let Aᵢ : Scheme := ((smallEtaleNeighborhoodOver X s).obj i).left
  let Cᵢ : Scheme := pullback ((smallEtaleNeighborhoodOver X s).obj i).hom p
  let g : Aᵢ ⟶ X.left := ((smallEtaleNeighborhoodOver X s).obj i).hom
  let σᵢ : Aᵢ ⟶ Cᵢ := etaleCurveOriginalSectionStage X s p σ hσ i
  let pr : Cᵢ ⟶ N := pullback.snd g p
  have hpr : σᵢ ≫ pr = g ≫ σ :=
    etaleCurveOriginalSectionStage_original X s p σ hσ i
  exact (Category.assoc σᵢ pr t).symm.trans
    ((congrArg (fun z : Aᵢ ⟶ N => z ≫ t) hpr).trans (Category.assoc g σ t))

/-- The original common geometric marking remains equal at every actual stage. -/
theorem etaleCurveOriginalSectionStages_same_marking
    (τ : X.left ⟶ N) (hτ : τ ≫ p = 𝟙 _)
    (hmark : s.hom ≫ σ = s.hom ≫ τ) (i : SmallEtaleNeighborhood X s) :
    etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i) ≫
        etaleCurveOriginalSectionStage X s p σ hσ i =
      etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i) ≫
        etaleCurveOriginalSectionStage X s p τ hτ i := by
  let Aᵢ : Scheme := ((smallEtaleNeighborhoodOver X s).obj i).left
  let Cᵢ : Scheme := pullback ((smallEtaleNeighborhoodOver X s).obj i).hom p
  let g : Aᵢ ⟶ X.left := ((smallEtaleNeighborhoodOver X s).obj i).hom
  let σᵢ : Aᵢ ⟶ Cᵢ := etaleCurveOriginalSectionStage X s p σ hσ i
  let τᵢ : Aᵢ ⟶ Cᵢ := etaleCurveOriginalSectionStage X s p τ hτ i
  let m : Spec (.of s.residueField) ⟶ Aᵢ :=
    etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i)
  have hm : m ≫ g = s.hom :=
    etaleNeighborhoodMark_hom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i)
  have hs₁ : σᵢ ≫ pullback.fst g p = 𝟙 Aᵢ :=
    etaleCurveOriginalSectionStage_projection X s p σ hσ i
  have ht₁ : τᵢ ≫ pullback.fst g p = 𝟙 Aᵢ :=
    etaleCurveOriginalSectionStage_projection X s p τ hτ i
  have hs₂ : σᵢ ≫ pullback.snd g p = g ≫ σ :=
    etaleCurveOriginalSectionStage_original X s p σ hσ i
  have ht₂ : τᵢ ≫ pullback.snd g p = g ≫ τ :=
    etaleCurveOriginalSectionStage_original X s p τ hτ i
  have hsproj : (m ≫ σᵢ) ≫ pullback.fst g p = m :=
    (Category.assoc m σᵢ _).trans
      ((congrArg (fun z : Aᵢ ⟶ Aᵢ => m ≫ z) hs₁).trans (Category.comp_id m))
  have htproj : (m ≫ τᵢ) ≫ pullback.fst g p = m :=
    (Category.assoc m τᵢ _).trans
      ((congrArg (fun z : Aᵢ ⟶ Aᵢ => m ≫ z) ht₁).trans (Category.comp_id m))
  have hsorig : (m ≫ σᵢ) ≫ pullback.snd g p = s.hom ≫ σ :=
    (Category.assoc m σᵢ _).trans
      ((congrArg (fun z : Aᵢ ⟶ N => m ≫ z) hs₂).trans
        ((Category.assoc m g σ).symm.trans
          (congrArg (fun z : Spec (.of s.residueField) ⟶ X.left => z ≫ σ) hm)))
  have htorig : (m ≫ τᵢ) ≫ pullback.snd g p = s.hom ≫ τ :=
    (Category.assoc m τᵢ _).trans
      ((congrArg (fun z : Aᵢ ⟶ N => m ≫ z) ht₂).trans
        ((Category.assoc m g τ).symm.trans
          (congrArg (fun z : Spec (.of s.residueField) ⟶ X.left => z ≫ τ) hm)))
  exact pullback.hom_ext (hsproj.trans htproj.symm)
    (hsorig.trans (hmark.trans htorig.symm))

include hσ in
/-- Actual inputs for the fixed-clopen producer from the original pair of sections. -/
theorem exists_etaleCurve_original_pair_at_stage
    (τ : X.left ⟶ N) (hτ : τ ≫ p = 𝟙 _)
    (hmark : s.hom ≫ σ = s.hom ≫ τ) (i : SmallEtaleNeighborhood X s) :
    ∃ (σi τi : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶
        (etaleCurveDiagram X s p).obj i),
      σi ≫ (etaleCurveStructure X s p).app i = 𝟙 _ ∧
      τi ≫ (etaleCurveStructure X s p).app i = 𝟙 _ ∧
      etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i) ≫ σi =
        etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i) ≫ τi ∧
      σi ≫ pullback.snd ((smallEtaleNeighborhoodOver X s).obj i).hom p =
        (etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i)).left ≫ σ ∧
      τi ≫ pullback.snd ((smallEtaleNeighborhoodOver X s).obj i).hom p =
        (etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i)).left ≫ τ := by
  exact ⟨etaleCurveOriginalSectionStage X s p σ hσ i,
    etaleCurveOriginalSectionStage X s p τ hτ i,
    etaleCurveOriginalSectionStage_projection X s p σ hσ i,
    etaleCurveOriginalSectionStage_projection X s p τ hτ i,
    etaleCurveOriginalSectionStages_same_marking X s p σ hσ τ hτ hmark i,
    etaleCurveOriginalSectionStage_original X s p σ hσ i,
    etaleCurveOriginalSectionStage_original X s p τ hτ i⟩
end AlgebraicGeometry.Scheme.SmoothSite
