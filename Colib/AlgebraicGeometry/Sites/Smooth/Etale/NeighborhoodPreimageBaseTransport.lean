/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEtalePreimage

/-! # Transport a component preimage at its actual base marking

The lower element is transported only along equality of the actual base points.
No second preimage is selected and no positive-dimensional existence is assumed
apart from the explicit input to this reflection lemma.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- A preimage stated at the component's own base point transports to the
original base point and reflects through the actual marked étale map. -/
theorem exists_original_preimage_of_etale_chart_preimage_at_own_base
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {A B T : SmoothSite S} [IsAffine A.left] [IsAffine B.left] [IsAffine T.left]
    (f : A ⟶ B) [Etale f.left] (g : B ⟶ T)
    (c : A ⟶ T) (hfactor : f ≫ g = c)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ B.left)
    (hf : ξ ≫ f.left = η)
    (Q : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (b : Q.obj (op B))
    (hcomponent : ∃ z : etaleNeighborhoodValue T (ξ ≫ c.left) Q,
      etaleNeighborhoodValuePullback c (ξ := ξ) rfl Q z =
        toEtaleNeighborhoodValueFromObject A ξ Q (Q.map f.op b)) :
    ∃ z : etaleNeighborhoodValue T (η ≫ g.left) Q,
      etaleNeighborhoodValuePullback g (ξ := η) rfl Q z =
        toEtaleNeighborhoodValueFromObject B η Q b := by
  subst c
  have hbase : ξ ≫ (f ≫ g).left = η ≫ g.left := by
    change ξ ≫ (f.left ≫ g.left) = η ≫ g.left
    rw [← Category.assoc, hf]
  have transport (ζ : Spec (.of Ω) ⟶ T.left) (hζ : ξ ≫ (f ≫ g).left = ζ) :
      ∃ z : etaleNeighborhoodValue T ζ Q,
        etaleNeighborhoodValuePullback (f ≫ g) hζ Q z =
          toEtaleNeighborhoodValueFromObject A ξ Q (Q.map f.op b) := by
    subst ζ
    exact hcomponent
  obtain ⟨z, hz⟩ := transport (η ≫ g.left) hbase
  exact ⟨z, original_preimage_of_etale_chart_preimage f g ξ η (η ≫ g.left)
    hf rfl Q b z hz⟩

end AlgebraicGeometry.Scheme.SmoothSite
