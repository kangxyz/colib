/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEtaleChange
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChart

/-!
# Original neighborhood restrictions for the two etale-chart sections

All objects remain in the original smooth site. The original representative and its
section-restricted lower-dimensional pullback are identified with the two actual chart
maps through the same canonical etale-change inverse. These formulas do not assert that
the restrictions are equal, nor extend the presheaf to a strict-local scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
open Opposite
variable {S : Scheme.{u}}
  {A Y Z : SmoothSite S} [IsAffine A.left] [IsAffine Y.left] [IsAffine Z.left]
  (q : A ⟶ Z) [Etale q.left] (p : Z ⟶ Y) (s : Y ⟶ Z)

/-- The actual coordinate-section pullback as an object of the original smooth site. -/
def sectionObject : SmoothSite S := mk (pullback.fst s.left q.left ≫ Y.hom)

/-- The original etale map from the section pullback to the lower-dimensional base. -/
def sectionToBase : sectionObject q s ⟶ Y := homMk (pullback.fst s.left q.left) rfl

/-- The original map from the section pullback to the chart. -/
def sectionToChart : sectionObject q s ⟶ A := homMk (pullback.snd s.left q.left) (by
  change pullback.snd s.left q.left ≫ A.hom = pullback.fst s.left q.left ≫ Y.hom
  rw [← MorphismProperty.Over.w q, ← Category.assoc, ← pullback.condition,
    Category.assoc, MorphismProperty.Over.w s])

/-- The actual etale chart refinement in the original smooth site. -/
def refinementObject : SmoothSite S :=
  mk (Scheme.EtaleChart.original q.left p.left s.left ≫ A.hom)

/-- The original etale projection to the chart. -/
def refinementToChart : refinementObject q p s ⟶ A :=
  homMk (Scheme.EtaleChart.original q.left p.left s.left) rfl

/-- The original projection to the coordinate-section pullback. -/
def refinementToSection : refinementObject q p s ⟶ sectionObject q s :=
  homMk (pullback.snd _ _) (by
    change pullback.snd (q.left ≫ p.left) (pullback.fst s.left q.left) ≫
      (pullback.fst s.left q.left ≫ Y.hom) =
      pullback.fst (q.left ≫ p.left) (pullback.fst s.left q.left) ≫ A.hom
    rw [← Category.assoc, ← pullback.condition, Category.assoc, Category.assoc,
      MorphismProperty.Over.w p, MorphismProperty.Over.w q])

instance : IsAffine (sectionObject q s).left := by
  change IsAffine (pullback s.left q.left)
  infer_instance
instance : IsAffine (refinementObject q p s).left := by
  change IsAffine (Scheme.EtaleChart.refinement q.left p.left s.left)
  infer_instance
instance : Etale (refinementToChart q p s).left := by
  change Etale (pullback.fst (q.left ≫ p.left) (pullback.fst s.left q.left))
  infer_instance

instance : Etale (sectionToBase q s).left := by
  change Etale (pullback.fst s.left q.left)
  infer_instance

/-- The two composites to the original tail base agree. -/
theorem refinement_square :
    refinementToSection q p s ≫ sectionToBase q s =
      refinementToChart q p s ≫ (q ≫ p) := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.condition.symm

variable {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ A.left)
  (η : Spec (.of Ω) ⟶ Y.left) (hξ : ξ ≫ q.left = η ≫ s.left)
  (hs : s.left ≫ p.left = 𝟙 Y.left)

/-- The unchanged scheme marking on the original section-pullback object. -/
abbrev sectionMark : Spec (.of Ω) ⟶ (sectionObject q s).left :=
  Scheme.EtaleChart.sectionMark q.left s.left ξ η hξ
/-- The unchanged scheme marking on the original refinement object. -/
abbrev refinementMark : Spec (.of Ω) ⟶ (refinementObject q p s).left :=
  Scheme.EtaleChart.refinementMark q.left p.left s.left ξ η hξ hs

omit [IsAffine A.left] [IsAffine Y.left] [IsAffine Z.left] in
/-- The section-pullback mark has the prescribed lower-dimensional image. -/
theorem sectionMark_base :
    sectionMark q s ξ η hξ ≫ (sectionToBase q s).left = η := pullback.lift_fst _ _ _

omit [IsAffine A.left] [IsAffine Y.left] [IsAffine Z.left] in
/-- The section-pullback mark recovers the original chart mark. -/
theorem sectionMark_chart :
    sectionMark q s ξ η hξ ≫ (sectionToChart q s).left = ξ := pullback.lift_snd _ _ _

/-- The refinement projection recovers the original chart mark. -/
theorem refinementMark_chart :
    refinementMark q p s ξ η hξ hs ≫ (refinementToChart q p s).left = ξ :=
  Scheme.EtaleChart.refinementMark_original q.left p.left s.left ξ η hξ hs

/-- The other projection recovers the original section-pullback mark. -/
theorem refinementMark_section :
    refinementMark q p s ξ η hξ hs ≫ (refinementToSection q p s).left =
      sectionMark q s ξ η hξ := pullback.lift_snd _ _ _

include hξ hs in
omit [IsAffine A.left] [IsAffine Y.left] [IsAffine Z.left] [Etale q.left] in
/-- The original chart mark projects to the prescribed lower-dimensional mark. -/
theorem chartMark_base : ξ ≫ (q ≫ p).left = η :=
  Scheme.EtaleChart.mark_base q.left p.left s.left ξ η hξ hs

variable [QuasiSeparatedSpace S] [IsSepClosed Ω]
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The exact original COL-1102 etale comparison for the constructed refinement. -/
def refinementValueIso :
    etaleNeighborhoodValue A ξ F ≅
      etaleNeighborhoodValue (refinementObject q p s) (refinementMark q p s ξ η hξ hs) F :=
  etaleNeighborhoodValueEtaleIso (refinementToChart q p s)
    (refinementMark_chart q p s ξ η hξ hs) F

/-- Original evaluation is the original projection restriction through the canonical
etale inverse. -/
theorem original_representative :
    toEtaleNeighborhoodValueFromObject A ξ F =
      F.map (refinementToChart q p s).op ≫
        toEtaleNeighborhoodValueFromObject (refinementObject q p s)
          (refinementMark q p s ξ η hξ hs) F ≫
        (refinementValueIso q p s ξ η hξ hs F).inv := by
  rw [← Category.assoc, ← toEtaleNeighborhoodValueFromObject_pullback]
  change _ = (_ ≫ (refinementValueIso q p s ξ η hξ hs F).hom) ≫ _
  simp

/-- The original lower-dimensional pullback becomes the other refinement projection. -/
theorem lower_pullback_refinement :
    (etaleNeighborhoodValueEtaleIso (sectionToBase q s)
      (sectionMark_base q s ξ η hξ) F).inv ≫
    etaleNeighborhoodValuePullback (q ≫ p)
      (chartMark_base q p s ξ η hξ hs) F ≫
    (refinementValueIso q p s ξ η hξ hs F).hom =
      etaleNeighborhoodValuePullback (refinementToSection q p s)
        (refinementMark_section q p s ξ η hξ hs) F := by
  change _ ≫ etaleNeighborhoodValuePullback (q ≫ p) _ F ≫
    etaleNeighborhoodValuePullback (refinementToChart q p s) _ F = _
  rw [← etaleNeighborhoodValuePullback_comp (refinementToChart q p s) (q ≫ p)
    (refinementMark_chart q p s ξ η hξ hs) (chartMark_base q p s ξ η hξ hs)]
  simp only [← refinement_square q p s]
  rw [etaleNeighborhoodValuePullback_comp (refinementToSection q p s) (sectionToBase q s)
      (refinementMark_section q p s ξ η hξ hs) (sectionMark_base q s ξ η hξ)]
  change (etaleNeighborhoodValueEtaleIso (sectionToBase q s) _ F).inv ≫
    (etaleNeighborhoodValueEtaleIso (sectionToBase q s) _ F).hom ≫ _ = _
  simp

/-- The section-restricted lower-dimensional class pulls back as the actual retract restriction. -/
theorem retract_representative :
    F.map (sectionToChart q s).op ≫
      toEtaleNeighborhoodValueFromObject (sectionObject q s) (sectionMark q s ξ η hξ) F ≫
      (etaleNeighborhoodValueEtaleIso (sectionToBase q s)
        (sectionMark_base q s ξ η hξ) F).inv ≫
      etaleNeighborhoodValuePullback (q ≫ p)
        (chartMark_base q p s ξ η hξ hs) F =
    F.map (refinementToSection q p s ≫ sectionToChart q s).op ≫
      toEtaleNeighborhoodValueFromObject (refinementObject q p s)
        (refinementMark q p s ξ η hξ hs) F ≫
      (refinementValueIso q p s ξ η hξ hs F).inv := by
  apply (cancel_mono (refinementValueIso q p s ξ η hξ hs F).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [lower_pullback_refinement, toEtaleNeighborhoodValueFromObject_pullback]
  simp only [op_comp, F.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
