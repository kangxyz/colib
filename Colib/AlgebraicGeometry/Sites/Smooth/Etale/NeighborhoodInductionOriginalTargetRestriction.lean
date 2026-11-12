/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodInductionPulledRepresentative

/-! # Original target restriction supplies the pulled representative preimage

Consume the original-target restriction on the actual terminal neighborhood.
Only the representative pulled back from B is used. No map from the retained
curve to A is required, and the lower-dimensional isomorphism stays explicit.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.EtaleChart

/-- The actual original-target restriction output is enough for the original
pulled-back representative, on the same chosen terminal neighborhood. -/
theorem exists_pulled_preimage_of_original_target_restriction
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {A B Y Z T : SmoothSite S} [IsAffine A.left] [IsAffine Y.left]
    [IsAffine Z.left] [IsAffine T.left]
    (q : A ⟶ Z) [Etale q.left] (p : Z ⟶ Y) (s : Y ⟶ Z) (g : Y ⟶ T)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Y.left)
    (ζ : Spec (.of Ω) ⟶ T.left)
    (hξ : ξ ≫ q.left = η ≫ s.left) (hs : s.left ≫ p.left = 𝟙 Y.left)
    (hg : η ≫ g.left = ζ) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    [IsIso (etaleNeighborhoodValuePullback g hg F)]
    (chart : A ⟶ B) (b : F.obj (op B))
    (hEq : ∃ Anew : EtaleNeighborhood (refinementObject q p s)
        (refinementMark q p s ξ η hξ hs),
      F.map (etaleNeighborhoodHom _ _ Anew ≫
          (refinementToChart q p s ≫ chart)).op =
        F.map (etaleNeighborhoodHom _ _ Anew ≫
          ((refinementToSection q p s ≫ sectionToChart q s) ≫ chart)).op) :
    ∃ z : etaleNeighborhoodValue T ζ F,
      etaleNeighborhoodValuePullback ((q ≫ p) ≫ g) (by
        change ξ ≫ ((q ≫ p).left ≫ g.left) = ζ
        rw [← Category.assoc, chartMark_base q p s ξ η hξ hs, hg]) F z =
          toEtaleNeighborhoodValueFromObject A ξ F (F.map chart.op b) := by
  obtain ⟨Anew, hMaps⟩ := hEq
  apply exists_pulled_representative_preimage_of_restriction_maps_eq
    q p s g ξ η ζ hξ hs hg F chart b Anew
  simpa only [Category.assoc] using hMaps

end AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
