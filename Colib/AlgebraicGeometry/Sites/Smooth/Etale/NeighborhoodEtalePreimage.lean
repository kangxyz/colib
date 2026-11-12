/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEtaleChange

/-! # Reflect a representative preimage through its actual marked étale chart

The element of the lower marked value is unchanged. This is the final reflection
step for an original representative, not the production of its lower preimage.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- A preimage of the pulled representative is already a preimage of the original
representative when the actual chart is étale and preserves the original mark. -/
theorem original_preimage_of_etale_chart_preimage
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {A B T : SmoothSite S} [IsAffine A.left] [IsAffine B.left] [IsAffine T.left]
    (f : A ⟶ B) [Etale f.left] (g : B ⟶ T)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ B.left)
    (ζ : Spec (.of Ω) ⟶ T.left) (hf : ξ ≫ f.left = η) (hg : η ≫ g.left = ζ)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (b : F.obj (op B)) (z : etaleNeighborhoodValue T ζ F)
    (hz : etaleNeighborhoodValuePullback (f ≫ g) (by
        change ξ ≫ (f.left ≫ g.left) = ζ
        rw [← Category.assoc, hf, hg]) F z =
      toEtaleNeighborhoodValueFromObject A ξ F (F.map f.op b)) :
    etaleNeighborhoodValuePullback g hg F z =
      toEtaleNeighborhoodValueFromObject B η F b := by
  rw [etaleNeighborhoodValuePullback_comp f g hf hg F] at hz
  have hnat := ConcreteCategory.congr_hom
    (toEtaleNeighborhoodValueFromObject_pullback f hf F) b
  have heq : etaleNeighborhoodValuePullback f hf F
      (etaleNeighborhoodValuePullback g hg F z) =
      etaleNeighborhoodValuePullback f hf F
        (toEtaleNeighborhoodValueFromObject B η F b) := hz.trans hnat.symm
  have h := congrArg (fun w => (etaleNeighborhoodValueEtaleIso f hf F).inv w) heq
  have hcancel := ConcreteCategory.congr_hom
    (etaleNeighborhoodValueEtaleIso f hf F).hom_inv_id
  exact (hcancel _).symm.trans (h.trans (hcancel _))

end AlgebraicGeometry.Scheme.SmoothSite
