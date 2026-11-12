/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.FixedClopenSectionPair

/-! # The component selected by the original common geometric marking

The point on the strict-local curve is constructed from its native Cartesian
square. Component descent supplies the preimage equation, and the actual stage
Cartesian squares supply both sections and their marking in that component.
Neither component membership nor the limit preimage equation is a hypothesis.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme

/-- Construct the actual section in a Cartesian square and identify its marked
value by the two genuine projections of the specified marked morphism. -/
theorem exists_cartesian_section_with_mark
    {C' C A' A T : Scheme.{u}}
    (F : C' ⟶ C) (q' : C' ⟶ A') (q : C ⟶ A) (b : A' ⟶ A)
    (hp : IsPullback F q' q b) (σ : A ⟶ C) (hσ : σ ≫ q = 𝟙 A)
    (ξ' : T ⟶ A') (ξ : T ⟶ A) (hξ : ξ' ≫ b = ξ)
    (m : T ⟶ C') (hmF : m ≫ F = ξ ≫ σ) (hmq : m ≫ q' = ξ') :
    ∃ σ' : A' ⟶ C', σ' ≫ F = b ≫ σ ∧ σ' ≫ q' = 𝟙 A' ∧ m = ξ' ≫ σ' := by
  let σ' := hp.lift (b ≫ σ) (𝟙 A')
    (by simp only [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  have hF : σ' ≫ F = b ≫ σ := hp.lift_fst _ _ _
  have hq : σ' ≫ q' = 𝟙 A' := hp.lift_snd _ _ _
  refine ⟨σ', hF, hq, ?_⟩
  apply hp.hom_ext
  · exact hmF.trans ((congrArg (fun z : T ⟶ A => z ≫ σ) hξ).symm.trans
      ((Category.assoc ξ' b σ).trans
        ((congrArg (fun z : A' ⟶ C => ξ' ≫ z) hF).symm.trans
          (Category.assoc ξ' σ' F).symm)))
  · exact hmq.trans ((Category.comp_id ξ').symm.trans
      ((congrArg (fun z : A' ⟶ A' => ξ' ≫ z) hq).symm.trans
        (Category.assoc ξ' σ' q').symm))

namespace SmoothSite

/-- Starting with the original whole-curve sections and their common marking,
choose the actual strict-local component and a finite stage containing both
marked values. The output discharges exactly hpre/hmem of FixedClopenSectionPair. -/
theorem exists_etaleCurve_marked_component_section_stage
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    [IsLocallyNoetherian X.left] [IsNormal N] [IsProper p]
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
          (IsLocalRing.closedPoint s.residueField)) ∈ U := by
  let c := etaleCurveCone X B hX s p
  let cA := smallEtaleNeighborhoodStrictHenselizationCone X B hX s
  let qL := pullback.fst (strictHenselizationToBase B X.left hX s) p
  let η := geometricPointToStrictHenselization B X.left hX s
  let ξ₀ := etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i₀)
  have hη₀ : η ≫ cA.π.app i₀ = ξ₀ :=
    geometricPointToStrictHenselization_comp_smallEtaleNeighborhoodCone_π X B hX s i₀
  have hw : (ξ₀ ≫ σ) ≫ (etaleCurveStructure X s p).app i₀ = η ≫ cA.π.app i₀ :=
    (Category.assoc ξ₀ σ _).trans
      ((congrArg (fun z : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i₀ ⟶
        (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i₀ => ξ₀ ≫ z) hσ).trans
        ((Category.comp_id ξ₀).trans hη₀.symm))
  let markL := (etaleCurveCone_isPullback X B hX s p i₀).lift (ξ₀ ≫ σ) η hw
  have hmarkLπ : markL ≫ c.π.app i₀ = ξ₀ ≫ σ :=
    (etaleCurveCone_isPullback X B hX s p i₀).lift_fst _ _ _
  have hmarkLq : markL ≫ qL = η :=
    (etaleCurveCone_isPullback X B hX s p i₀).lift_snd _ _ _
  let x := markL (IsLocalRing.closedPoint s.residueField)
  obtain ⟨i, e, hpre⟩ := exists_etaleCurve_normalComponent_preimage_eq_over X B hX s p x i₀
  let ξ := etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i)
  let b := (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map e
  let F := (etaleCurveDiagram X s p).map e
  let qi := (etaleCurveStructure X s p).app i
  let m := markL ≫ c.π.app i
  have hξ : ξ ≫ b = ξ₀ :=
    etaleNeighborhoodMark_map X s.hom ((smallEtaleNeighborhoodInclusion X s).map e)
  have hmF : m ≫ F = ξ₀ ≫ σ :=
    (Category.assoc markL (c.π.app i) F).trans
      ((congrArg (fun z : c.pt ⟶ (etaleCurveDiagram X s p).obj i₀ =>
        markL ≫ z) (c.w e)).trans hmarkLπ)
  have hmq : m ≫ qi = ξ :=
    (Category.assoc markL (c.π.app i) qi).trans
      ((congrArg (fun z : c.pt ⟶
        (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i => markL ≫ z)
        (etaleCurveCone_π_fst X B hX s p i)).trans
      ((Category.assoc markL qL (cA.π.app i)).symm.trans
      ((congrArg (fun z : Spec (.of s.residueField) ⟶ cA.pt => z ≫ cA.π.app i) hmarkLq).trans
        (geometricPointToStrictHenselization_comp_smallEtaleNeighborhoodCone_π X B hX s i))))
  obtain ⟨σi, hsF, hsq, hms⟩ := exists_cartesian_section_with_mark
    F qi ((etaleCurveStructure X s p).app i₀) b (etaleCurveDiagram_isPullback X s p e)
    σ hσ ξ ξ₀ hξ m hmF hmq
  obtain ⟨τi, htF, htq, hmt⟩ := exists_cartesian_section_with_mark
    F qi ((etaleCurveStructure X s p).app i₀) b (etaleCurveDiagram_isPullback X s p e)
    τ hτ ξ ξ₀ hξ m (hmF.trans hmark) hmq
  have hpoint : c.π.app i x = σi (ξ (IsLocalRing.closedPoint s.residueField)) :=
    congrArg (fun z : Spec (.of s.residueField) ⟶ (etaleCurveDiagram X s p).obj i =>
      z (IsLocalRing.closedPoint s.residueField)) hms
  have hmem : σi (ξ (IsLocalRing.closedPoint s.residueField)) ∈ normalComponentOpen (c.π.app i x) :=
    (congrArg (fun z => z ∈ normalComponentOpen (c.π.app i x)) hpoint).mp
      (mem_normalComponentOpen _)
  exact ⟨markL, hmarkLq, hmarkLπ, i, e, hpre, σi, τi, hsF, htF, hsq, htq,
    hms.symm.trans hmt, hmem⟩

end SmoothSite
end AlgebraicGeometry.Scheme
