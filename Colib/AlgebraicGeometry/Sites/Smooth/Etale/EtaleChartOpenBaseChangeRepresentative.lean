/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartOpenBaseChangeSmoothSite
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEtaleChange

/-! # Recover the original representative from the localized chart

The actual chart projection is an open immersion over the unchanged base S.
Its native marked-neighborhood isomorphism transports the localized pullback
of the original element back to the original chart representative. No retained
target map is reversed and no presheaf is extended to another base field.
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

/-- The actual projection to the original chart is the base change of the good open. -/
instance chartToOriginal_isOpenImmersion : IsOpenImmersion (chartToOriginal q p k).left :=
  inferInstanceAs (IsOpenImmersion (pullback.snd k (q.left ≫ p.left)))

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Y.left)
  (hξ : ξ ≫ q.left = η ≫ s.left)
  (ηV : Spec (.of Ω) ⟶ V) (hη : ηV ≫ k = η)
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The localized representative is the native pullback of the original one. -/
theorem target_representative_pullback {B : SmoothSite S} (t : A ⟶ B)
    (b : F.obj (op B)) :
    etaleNeighborhoodValuePullback (chartToOriginal q p k)
        (mark_original q p s hs k ξ η hξ ηV hη) F
        (toEtaleNeighborhoodValueFromObject A ξ F (F.map t.op b)) =
      toEtaleNeighborhoodValueFromObject (chartSite q p k)
        (mark q p s hs k ξ η hξ ηV hη) F (F.map (target q p k t).op b) := by
  have h := ConcreteCategory.congr_hom
    (toEtaleNeighborhoodValueFromObject_pullback (chartToOriginal q p k)
      (mark_original q p s hs k ξ η hξ ηV hη) F) (F.map t.op b)
  simpa only [target, op_comp, F.map_comp, ConcreteCategory.comp_apply] using h

/-- Applying the actual etale inverse recovers the same original representative. -/
theorem target_representative_recovery {B : SmoothSite S} (t : A ⟶ B)
    (b : F.obj (op B)) :
    (etaleNeighborhoodValueEtaleIso (chartToOriginal q p k)
      (mark_original q p s hs k ξ η hξ ηV hη) F).inv
      (toEtaleNeighborhoodValueFromObject (chartSite q p k)
        (mark q p s hs k ξ η hξ ηV hη) F (F.map (target q p k t).op b)) =
      toEtaleNeighborhoodValueFromObject A ξ F (F.map t.op b) := by
  rw [← target_representative_pullback q p s hs k ξ η hξ ηV hη F t b]
  exact ConcreteCategory.congr_hom
    (etaleNeighborhoodValueEtaleIso (chartToOriginal q p k)
      (mark_original q p s hs k ξ η hξ ηV hη) F).hom_inv_id
    (toEtaleNeighborhoodValueFromObject A ξ F (F.map t.op b))

end AlgebraicGeometry.Scheme.SmoothSite.EtaleChart.OpenBaseChange
