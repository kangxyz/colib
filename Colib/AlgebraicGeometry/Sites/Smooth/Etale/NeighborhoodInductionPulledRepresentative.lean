/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodInductionAction

/-! # Induction for a representative pulled back from the actual retained target

The retained curve need only map to the original target B, not to the etale chart A.
The action equality on B is applied to the original element of F(B). Functoriality
then gives exactly the equality needed for its pullback to A. This does not assert
an equality on all of F(A), and leaves the lower-dimensional isomorphism explicit.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.EtaleChart

/-- Target-level equality on the original element suffices for its chart pullback.
No morphism from the retained curve to the chart is required. -/
theorem exists_pulled_representative_preimage_of_restrictions_eq
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
    (N : EtaleNeighborhood (refinementObject q p s) (refinementMark q p s ξ η hξ hs))
    (hb : (F.map ((etaleNeighborhoodHom _ _ N ≫ refinementToChart q p s) ≫
        chart).op).hom b =
      (F.map ((etaleNeighborhoodHom _ _ N ≫
        (refinementToSection q p s ≫ sectionToChart q s)) ≫ chart).op).hom b) :
    ∃ z : etaleNeighborhoodValue T ζ F,
      etaleNeighborhoodValuePullback ((q ≫ p) ≫ g) (by
        change ξ ≫ ((q ≫ p).left ≫ g.left) = ζ
        rw [← Category.assoc, chartMark_base q p s ξ η hξ hs, hg]) F z =
          toEtaleNeighborhoodValueFromObject A ξ F (F.map chart.op b) := by
  apply exists_representative_preimage_of_restrictions_eq
    q p s g ξ η ζ hξ hs hg F (F.map chart.op b) N
  simpa only [op_comp, F.map_comp, ConcreteCategory.comp_apply] using hb

/-- An equality of the two restriction homomorphisms into the original target
is used only on the original representative, not on every chart section. -/
theorem exists_pulled_representative_preimage_of_restriction_maps_eq
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
    (N : EtaleNeighborhood (refinementObject q p s) (refinementMark q p s ξ η hξ hs))
    (hMaps : F.map ((etaleNeighborhoodHom _ _ N ≫ refinementToChart q p s) ≫
        chart).op =
      F.map ((etaleNeighborhoodHom _ _ N ≫
        (refinementToSection q p s ≫ sectionToChart q s)) ≫ chart).op) :
    ∃ z : etaleNeighborhoodValue T ζ F,
      etaleNeighborhoodValuePullback ((q ≫ p) ≫ g) (by
        change ξ ≫ ((q ≫ p).left ≫ g.left) = ζ
        rw [← Category.assoc, chartMark_base q p s ξ η hξ hs, hg]) F z =
          toEtaleNeighborhoodValueFromObject A ξ F (F.map chart.op b) := by
  exact exists_pulled_representative_preimage_of_restrictions_eq
    q p s g ξ η ζ hξ hs hg F chart b N (ConcreteCategory.congr_hom hMaps b)

end AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
