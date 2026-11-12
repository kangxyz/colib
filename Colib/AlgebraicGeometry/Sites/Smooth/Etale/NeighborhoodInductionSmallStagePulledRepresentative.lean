/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodInductionSmallStageAction
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodInductionPulledRepresentative

/-! # Actual small-stage action on a pulled-back original representative

The terminal target is B. Only the original element of F(B) is pulled back to
its chart A; no extension of the retained target map to A is assumed. The same
actual terminal neighborhood and stage morphism are used throughout.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.EtaleChart

/-- Normalize the actual small-stage output on B and apply it to the original
representative. The lower-dimensional isomorphism remains an explicit input. -/
theorem exists_pulled_representative_preimage_of_small_stage_restriction
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {A B Y Z T : SmoothSite S} [IsAffine A.left] [IsAffine Y.left]
    [IsAffine Z.left] [IsAffine T.left]
    (q : A ⟶ Z) [Etale q.left] (p : Z ⟶ Y) (s : Y ⟶ Z) (g : Y ⟶ T)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Y.left)
    (ζ : Spec (.of Ω) ⟶ T.left)
    (hξ : ξ ≫ q.left = η ≫ s.left) (hs : s.left ≫ p.left = 𝟙 Y.left)
    (hg : η ≫ g.left = ζ) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    [IsIso (etaleNeighborhoodValuePullback g hg F)] (chart : A ⟶ B) (b : F.obj (op B))
    (i : SmallEtaleNeighborhood (refinementObject q p s)
      (refinementGeometricPoint q p s ξ η hξ hs))
    (hOutput :
      let X := refinementObject q p s
      let sRef := refinementGeometricPoint q p s ξ η hξ hs
      let fixedHom := etaleNeighborhoodHom X sRef.hom
        ((smallEtaleNeighborhoodInclusion X sRef).obj i)
      let f₀ := fixedHom ≫ (refinementToChart q p s ≫ chart)
      let g₀ := fixedHom ≫ ((refinementToSection q p s ≫ sectionToChart q s) ≫ chart)
      ∃ (ℓ : CategoryTheory.Over i) (Anew : EtaleNeighborhood X sRef.hom)
        (v : Anew ⟶ (smallEtaleNeighborhoodInclusion X sRef).obj ℓ.left),
        F.map (((etaleNeighborhoodToSmooth X sRef.hom).map v) ≫
            ((smallEtaleNeighborhoodToSmooth X sRef).map ℓ.hom ≫ f₀)).op =
          F.map (((etaleNeighborhoodToSmooth X sRef.hom).map v) ≫
            ((smallEtaleNeighborhoodToSmooth X sRef).map ℓ.hom ≫ g₀)).op) :
    ∃ z : etaleNeighborhoodValue T ζ F,
      etaleNeighborhoodValuePullback ((q ≫ p) ≫ g) (by
        change ξ ≫ ((q ≫ p).left ≫ g.left) = ζ
        rw [← Category.assoc, chartMark_base q p s ξ η hξ hs, hg]) F z =
          toEtaleNeighborhoodValueFromObject A ξ F (F.map chart.op b) := by
  obtain ⟨ℓ, Anew, v, hMaps⟩ := hOutput
  apply exists_pulled_representative_preimage_of_restriction_maps_eq
    q p s g ξ η ζ hξ hs hg F chart b Anew
  have hFinal := etaleNeighborhood_restriction_maps_eq_of_stage
    (refinementMark q p s ξ η hξ hs) F
    (refinementToChart q p s ≫ chart)
    ((refinementToSection q p s ≫ sectionToChart q s) ≫ chart) v
    ((smallEtaleNeighborhoodToSmooth (refinementObject q p s)
      (refinementGeometricPoint q p s ξ η hξ hs)).map ℓ.hom ≫
      (etaleNeighborhoodHom _ _ ((smallEtaleNeighborhoodInclusion _ _).obj i) ≫
        (refinementToChart q p s ≫ chart)))
    ((smallEtaleNeighborhoodToSmooth (refinementObject q p s)
      (refinementGeometricPoint q p s ξ η hξ hs)).map ℓ.hom ≫
      (etaleNeighborhoodHom _ _ ((smallEtaleNeighborhoodInclusion _ _).obj i) ≫
        ((refinementToSection q p s ≫ sectionToChart q s) ≫ chart)))
    (by rw [← Category.assoc, smallEtaleNeighborhoodMap_comp_hom])
    (by rw [← Category.assoc, smallEtaleNeighborhoodMap_comp_hom]) hMaps
  simpa only [Category.assoc] using hFinal

end AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
