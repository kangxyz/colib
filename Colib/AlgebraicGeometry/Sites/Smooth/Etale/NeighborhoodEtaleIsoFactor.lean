/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEtaleChange

/-! # Actual étale factors preserve and reflect marked structural isomorphisms -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Transport only the target marking equality of an actual pullback. -/
theorem isIso_etaleNeighborhoodValuePullback_of_target_eq
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {X T : SmoothSite S} [IsAffine X.left] [IsAffine T.left]
    (g : X ⟶ T) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X.left) (ζ : Spec (.of Ω) ⟶ T.left)
    (hg : ξ ≫ g.left = ζ)
    (Q : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (h : IsIso (etaleNeighborhoodValuePullback g (ξ := ξ) rfl Q)) :
    IsIso (etaleNeighborhoodValuePullback g hg Q) := by
  subst ζ
  exact h

/-- Cancel the actual étale pullback, retaining all three markings. -/
theorem isIso_etaleNeighborhoodValuePullback_comp_iff
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {A B T : SmoothSite S} [IsAffine A.left] [IsAffine B.left] [IsAffine T.left]
    (f : A ⟶ B) [Etale f.left] (g : B ⟶ T)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ B.left)
    (ζ : Spec (.of Ω) ⟶ T.left) (hf : ξ ≫ f.left = η) (hg : η ≫ g.left = ζ)
    (Q : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso (etaleNeighborhoodValuePullback (f ≫ g) (ξ := ξ) (η := ζ) (by
      change ξ ≫ (f.left ≫ g.left) = ζ
      rw [← Category.assoc, hf, hg]) Q) ↔
      IsIso (etaleNeighborhoodValuePullback g hg Q) := by
  rw [etaleNeighborhoodValuePullback_comp f g hf hg Q]
  let : IsIso (etaleNeighborhoodValuePullback f hf Q) :=
    (etaleNeighborhoodValueEtaleIso f hf Q).isIso_hom
  exact isIso_comp_right_iff _ _

/-- Transfer a structural isomorphism across an actual marked étale span. -/
theorem isIso_etaleNeighborhoodValuePullback_of_etale_span
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {A X Y T : SmoothSite S}
    [IsAffine A.left] [IsAffine X.left] [IsAffine Y.left] [IsAffine T.left]
    (f : A ⟶ X) [Etale f.left] (c : A ⟶ Y) [Etale c.left]
    (gX : X ⟶ T) (gY : Y ⟶ T) (hfactor : c ≫ gY = f ≫ gX)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (η : Spec (.of Ω) ⟶ A.left) (ξ : Spec (.of Ω) ⟶ X.left)
    (θ : Spec (.of Ω) ⟶ Y.left) (ζ : Spec (.of Ω) ⟶ T.left)
    (hf : η ≫ f.left = ξ) (hc : η ≫ c.left = θ)
    (hX : ξ ≫ gX.left = ζ) (hY : θ ≫ gY.left = ζ)
    (Q : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hi : IsIso (etaleNeighborhoodValuePullback gY hY Q)) :
    IsIso (etaleNeighborhoodValuePullback gX hX Q) := by
  have h := (isIso_etaleNeighborhoodValuePullback_comp_iff c gY η θ ζ hc hY Q).mpr hi
  apply (isIso_etaleNeighborhoodValuePullback_comp_iff f gX η ξ ζ hf hX Q).mp
  have transport (m : A ⟶ T) (hm : c ≫ gY = m)
      (hmark : η ≫ m.left = ζ) :
      IsIso (etaleNeighborhoodValuePullback m hmark Q) := by
    subst m
    exact h
  exact transport _ hfactor _

end AlgebraicGeometry.Scheme.SmoothSite
