/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.EtaleChartOpenBaseChangeRepresentative
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodCurveSections

/-! # Recover the original lower preimage from the good-open chart

The lower map is the original lower map composed with the actual good-open
inclusion. The literal pullback square identifies the two total maps. The
native etale neighborhood isomorphism then reflects the preimage equality,
keeping the same element of the original lower marked value.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.EtaleChart.OpenBaseChange

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] {A Y Z : SmoothSite S}
  [IsAffine A.left] [IsAffine Y.left] [IsAffine Z.left]
  (q : A ⟶ Z) [Etale q.left] (p : Z ⟶ Y) [Smooth p.left]
  (s : Y ⟶ Z) (hs : s.left ≫ p.left = 𝟙 Y.left)
  {V : Scheme.{u}} [IsAffine V] (k : V ⟶ Y.left) [IsOpenImmersion k]

omit [QuasiSeparatedSpace S] in
/-- The good tail maps to the original tail over the unchanged base. -/
def tailToOriginal : tailSite k ⟶ Y := homMk k rfl

omit [QuasiSeparatedSpace S] in
/-- The actual chart and tail projections commute with the original curve map. -/
theorem chart_projection_square :
    chartToOriginal q p k ≫ (q ≫ p) =
      (chart q p k ≫ projection p k) ≫ tailToOriginal k := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.snd k (q.left ≫ p.left) ≫ (q.left ≫ p.left) =
    (Scheme.EtaleChart.MarkedBaseChange.chartMap q.left p.left k ≫
      Scheme.EtaleChart.MarkedBaseChange.projection p.left k) ≫ k
  rw [Scheme.EtaleChart.MarkedBaseChange.chartMap_fst]
  exact (pullback.condition (f := k) (g := q.left ≫ p.left)).symm

omit [QuasiSeparatedSpace S] in
/-- The localized total lower map is the original total lower map after the
actual chart projection. -/
theorem lower_composite_square {T : SmoothSite S} (g : Y ⟶ T) :
    ((chart q p k ≫ projection p k) ≫ (tailToOriginal k ≫ g)) =
      chartToOriginal q p k ≫ ((q ≫ p) ≫ g) := by
  rw [← Category.assoc, ← chart_projection_square, Category.assoc]

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Y.left)
  (hξ : ξ ≫ q.left = η ≫ s.left)
  (ηV : Spec (.of Ω) ⟶ V) (hη : ηV ≫ k = η)

omit [IsSepClosed Ω] [QuasiSeparatedSpace S] in
/-- The original marking is preserved by the actual total lower map. -/
theorem lower_composite_mark {T : SmoothSite S} (g : Y ⟶ T)
    (ζ : Spec (.of Ω) ⟶ T.left) (hg : η ≫ g.left = ζ) :
    mark q p s hs k ξ η hξ ηV hη ≫
      ((chart q p k ≫ projection p k) ≫ (tailToOriginal k ≫ g)).left = ζ := by
  rw [lower_composite_square]
  change _ ≫ ((chartToOriginal q p k).left ≫ ((q ≫ p) ≫ g).left) = _
  rw [← Category.assoc, mark_original]
  change ξ ≫ ((q ≫ p).left ≫ g.left) = ζ
  rw [← Category.assoc, chartMark_base q p s ξ η hξ hs, hg]

/-- A localized lower preimage gives an original lower preimage with exactly
the same witness. No lower isomorphism is discharged by this recovery step. -/
theorem original_preimage_of_localized_preimage
    {B T : SmoothSite S} [IsAffine T.left] (g : Y ⟶ T)
    (ζ : Spec (.of Ω) ⟶ T.left) (hg : η ≫ g.left = ζ)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (t : A ⟶ B)
    (b : F.obj (op B)) (z : etaleNeighborhoodValue T ζ F)
    (hz : etaleNeighborhoodValuePullback
        ((chart q p k ≫ projection p k) ≫ (tailToOriginal k ≫ g))
        (lower_composite_mark q p s hs k ξ η hξ ηV hη g ζ hg) F z =
      toEtaleNeighborhoodValueFromObject (chartSite q p k)
        (mark q p s hs k ξ η hξ ηV hη) F (F.map (target q p k t).op b)) :
    etaleNeighborhoodValuePullback ((q ≫ p) ≫ g) (by
      change ξ ≫ ((q ≫ p).left ≫ g.left) = ζ
      rw [← Category.assoc, chartMark_base q p s ξ η hξ hs, hg]) F z =
      toEtaleNeighborhoodValueFromObject A ξ F (F.map t.op b) := by
  have hTotal : ξ ≫ ((q ≫ p) ≫ g).left = ζ := by
    change ξ ≫ ((q ≫ p).left ≫ g.left) = ζ
    rw [← Category.assoc, chartMark_base q p s ξ η hξ hs, hg]
  simp only [lower_composite_square] at hz
  rw [etaleNeighborhoodValuePullback_comp (chartToOriginal q p k)
    ((q ≫ p) ≫ g) (mark_original q p s hs k ξ η hξ ηV hη) hTotal] at hz
  have h := congrArg
    (fun w => (etaleNeighborhoodValueEtaleIso (chartToOriginal q p k)
      (mark_original q p s hs k ξ η hξ ηV hη) F).inv w) hz
  have hCancel := ConcreteCategory.congr_hom
    (etaleNeighborhoodValueEtaleIso (chartToOriginal q p k)
      (mark_original q p s hs k ξ η hξ ηV hη) F).hom_inv_id
    (etaleNeighborhoodValuePullback ((q ≫ p) ≫ g) hTotal F z)
  exact hCancel.symm.trans (h.trans
    (target_representative_recovery q p s hs k ξ η hξ ηV hη F t b))

end AlgebraicGeometry.Scheme.SmoothSite.EtaleChart.OpenBaseChange
