/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartOriginalFixedInputs
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartLocalizedRetainedLift
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodInductionOriginalTargetRestriction
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.EtaleChartOpenBaseChangePreimage

/-! # Localized original-target restriction returns the same original lower preimage

The input is the actual restriction equality, not an extra geometry certificate.
The lower-dimensional isomorphism remains an explicit induction hypothesis.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.EtaleChart.OpenBaseChange

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]
  {A Y Z B T : SmoothSite S}
  [IsAffine A.left] [IsAffine Y.left] [IsAffine Z.left] [IsAffine T.left]
  (q : A ⟶ Z) [Etale q.left] (p : Z ⟶ Y) [Smooth p.left]
  (s : Y ⟶ Z) (hs : s.left ≫ p.left = 𝟙 Y.left)
  {V : Scheme.{u}} [IsAffine V] (k : V ⟶ Y.left) [IsOpenImmersion k]

omit [QuasiSeparatedSpace S] [IsAffine T.left] in
/-- The actual nested retained lift gives precisely the old chart target after
localization. Its over-base proof is the one returned by the actual consumer. -/
theorem localizedRetained_chartTarget_eq
    {U N : Scheme.{u}} (i : A.left ⟶ U) (f : U ⟶ Y.left)
    (hi : i ≫ f = q.left ≫ p.left) (j : U ⟶ N) (fN : N ⟶ Y.left)
    (hj : j ≫ fN = f) (t : U ⟶ B.left) (ht : t ≫ B.hom = f ≫ Y.hom)
    (htt : (pullback.snd (pullback.snd k fN) j ≫ t) ≫ B.hom =
      Scheme.EtaleChart.LocalizedRetainedLift.retainedProjection k j fN ≫ (k ≫ Y.hom)) :
    OriginalFixed.chartTarget (chart q p k) (projection p k)
      (Scheme.EtaleChart.LocalizedRetainedLift.inclusion q.left p.left k i f hi j fN hj)
      (Scheme.EtaleChart.LocalizedRetainedLift.retainedProjection k j fN)
      (Scheme.EtaleChart.LocalizedRetainedLift.inclusion_structure
        q.left p.left k i f hi j fN hj)
      (pullback.snd (pullback.snd k fN) j ≫ t) htt =
    target q p k (OriginalFixed.chartTarget q p i f hi t ht) := by
  apply MorphismProperty.Over.Hom.ext
  exact Scheme.EtaleChart.LocalizedRetainedLift.inclusion_target
    q.left p.left k i f hi j fN hj t

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Y.left)
  (hξ : ξ ≫ q.left = η ≫ s.left)
  (ηV : Spec (.of Ω) ⟶ V) (hη : ηV ≫ k = η)

/-- Apply the existing induction consumer on the actual good-open chart, then
reflect its equality back to the original chart using exactly the same z. -/
theorem exists_original_preimage_of_localized_target_restriction
    (g : Y ⟶ T) (ζ : Spec (.of Ω) ⟶ T.left) (hg : η ≫ g.left = ζ)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    [IsIso (etaleNeighborhoodValuePullback g hg F)]
    (originalChart : A ⟶ B) (b : F.obj (op B))
    (hEq : ∃ Anew : EtaleNeighborhood
        (refinementObject (chart q p k) (projection p k) (sectionMap p s hs k))
        (refinementMark (chart q p k) (projection p k) (sectionMap p s hs k)
          (mark q p s hs k ξ η hξ ηV hη) ηV
          (mark_chart q p s hs k ξ η hξ ηV hη)
          (Scheme.EtaleChart.MarkedBaseChange.sectionMap_projection p.left s.left hs k)),
      F.map (etaleNeighborhoodHom _ _ Anew ≫
        (refinementToChart (chart q p k) (projection p k) (sectionMap p s hs k) ≫
          target q p k originalChart)).op =
      F.map (etaleNeighborhoodHom _ _ Anew ≫
        ((refinementToSection (chart q p k) (projection p k) (sectionMap p s hs k) ≫
          sectionToChart (chart q p k) (sectionMap p s hs k)) ≫
            target q p k originalChart)).op) :
    ∃ z : etaleNeighborhoodValue T ζ F,
      etaleNeighborhoodValuePullback ((q ≫ p) ≫ g) (by
        change ξ ≫ ((q ≫ p).left ≫ g.left) = ζ
        rw [← Category.assoc, chartMark_base q p s ξ η hξ hs, hg]) F z =
      toEtaleNeighborhoodValueFromObject A ξ F (F.map originalChart.op b) := by
  have hgV : ηV ≫ (tailToOriginal k ≫ g).left = ζ := by
    change ηV ≫ (k ≫ g.left) = ζ
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ g.left) hη).trans hg)
  have htail : ηV ≫ (tailToOriginal k).left = η := hη
  let : Etale (tailToOriginal k).left := inferInstanceAs (Etale k)
  let : IsIso (etaleNeighborhoodValuePullback (tailToOriginal k) htail F) :=
    (etaleNeighborhoodValueEtaleIso (tailToOriginal k) htail F).isIso_hom
  have hcomp := etaleNeighborhoodValuePullback_comp (tailToOriginal k) g htail hg F
  let : IsIso (etaleNeighborhoodValuePullback (tailToOriginal k ≫ g) hgV F) := by
    rw [hcomp]
    infer_instance
  obtain ⟨z, hz⟩ := exists_pulled_preimage_of_original_target_restriction
    (chart q p k) (projection p k) (sectionMap p s hs k) (tailToOriginal k ≫ g)
    (mark q p s hs k ξ η hξ ηV hη) ηV ζ
    (mark_chart q p s hs k ξ η hξ ηV hη)
    (Scheme.EtaleChart.MarkedBaseChange.sectionMap_projection p.left s.left hs k)
    hgV F (target q p k originalChart) b hEq
  exact ⟨z, original_preimage_of_localized_preimage q p s hs k ξ η hξ ηV hη
    g ζ hg F originalChart b z hz⟩

/-- Consume the literal nested-retained restriction output directly. The returned
z is the one produced by lower induction on the localized chart. -/
theorem exists_original_preimage_of_nested_retained_restriction
    (g : Y ⟶ T) (ζ : Spec (.of Ω) ⟶ T.left) (hg : η ≫ g.left = ζ)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    [IsIso (etaleNeighborhoodValuePullback g hg F)]
    {U N : Scheme.{u}} (i : A.left ⟶ U) (f : U ⟶ Y.left)
    (hi : i ≫ f = q.left ≫ p.left) (j : U ⟶ N) (fN : N ⟶ Y.left)
    (hj : j ≫ fN = f) (t : U ⟶ B.left) (ht : t ≫ B.hom = f ≫ Y.hom)
    (b : F.obj (op B))
    (hEq : ∃ (htt : (pullback.snd (pullback.snd k fN) j ≫ t) ≫ B.hom =
        Scheme.EtaleChart.LocalizedRetainedLift.retainedProjection k j fN ≫ (k ≫ Y.hom)),
      ∃ Anew : EtaleNeighborhood
        (refinementObject (chart q p k) (projection p k) (sectionMap p s hs k))
        (refinementMark (chart q p k) (projection p k) (sectionMap p s hs k)
          (mark q p s hs k ξ η hξ ηV hη) ηV
          (mark_chart q p s hs k ξ η hξ ηV hη)
          (Scheme.EtaleChart.MarkedBaseChange.sectionMap_projection p.left s.left hs k)),
      F.map (etaleNeighborhoodHom _ _ Anew ≫
        (refinementToChart (chart q p k) (projection p k) (sectionMap p s hs k) ≫
          (OriginalFixed.chartTarget (chart q p k) (projection p k)
          (Scheme.EtaleChart.LocalizedRetainedLift.inclusion q.left p.left k i f hi j fN hj)
          (Scheme.EtaleChart.LocalizedRetainedLift.retainedProjection k j fN)
          (Scheme.EtaleChart.LocalizedRetainedLift.inclusion_structure
            q.left p.left k i f hi j fN hj)
          (pullback.snd (pullback.snd k fN) j ≫ t) htt))).op =
      F.map (etaleNeighborhoodHom _ _ Anew ≫
        ((refinementToSection (chart q p k) (projection p k) (sectionMap p s hs k) ≫
          sectionToChart (chart q p k) (sectionMap p s hs k)) ≫
            (OriginalFixed.chartTarget (chart q p k) (projection p k)
          (Scheme.EtaleChart.LocalizedRetainedLift.inclusion q.left p.left k i f hi j fN hj)
          (Scheme.EtaleChart.LocalizedRetainedLift.retainedProjection k j fN)
          (Scheme.EtaleChart.LocalizedRetainedLift.inclusion_structure
            q.left p.left k i f hi j fN hj)
          (pullback.snd (pullback.snd k fN) j ≫ t) htt))).op) :
    ∃ z : etaleNeighborhoodValue T ζ F,
      etaleNeighborhoodValuePullback ((q ≫ p) ≫ g) (by
        change ξ ≫ ((q ≫ p).left ≫ g.left) = ζ
        rw [← Category.assoc, chartMark_base q p s ξ η hξ hs, hg]) F z =
      toEtaleNeighborhoodValueFromObject A ξ F
        (F.map (OriginalFixed.chartTarget q p i f hi t ht).op b) := by
  obtain ⟨htt, Anew, hMaps⟩ := hEq
  have hchart := localizedRetained_chartTarget_eq q p k i f hi j fN hj t ht htt
  apply exists_original_preimage_of_localized_target_restriction
    q p s hs k ξ η hξ ηV hη g ζ hg F (OriginalFixed.chartTarget q p i f hi t ht) b
  exact ⟨Anew, by simpa only [hchart] using hMaps⟩

end AlgebraicGeometry.Scheme.SmoothSite.EtaleChart.OpenBaseChange
