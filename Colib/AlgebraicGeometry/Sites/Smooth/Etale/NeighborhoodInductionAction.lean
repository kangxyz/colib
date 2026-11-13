/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodInductionStep

/-! # Apply the actual S1 restriction equality to the original representative

The same final marked neighborhood is retained through the stage morphism.
An equality of the two original restriction homomorphisms is evaluated at the
original representative, then passed to the existing induction-step consumer.
The lower-dimensional pullback isomorphism remains an explicit assumption.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- A stage refinement composes with the actual neighborhood map, as a morphism
in the original smooth site, not just as a map of underlying schemes. -/
theorem etaleNeighborhoodMap_comp_hom
    {S : Scheme.{u}} [QuasiSeparatedSpace S] {X : SmoothSite S}
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X.left)
    {N N₀ : EtaleNeighborhood X ξ} (v : N ⟶ N₀) :
    (etaleNeighborhoodToSmooth X ξ).map v ≫ etaleNeighborhoodHom X ξ N₀ =
      etaleNeighborhoodHom X ξ N := by
  apply MorphismProperty.Over.Hom.ext
  exact etaleNeighborhoodMap_hom X ξ v

/-- Normalize the terminal action equality to the original maps on the same
actual final neighborhood. The stage maps are identified by their actual
composite formulas; no new final map or compatibility producer is supplied. -/
theorem etaleNeighborhood_restriction_maps_eq_of_stage
    {S : Scheme.{u}} [QuasiSeparatedSpace S] {X Y : SmoothSite S}
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X.left)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (f₀ g₀ : X ⟶ Y)
    {N N₀ : EtaleNeighborhood X ξ} (v : N ⟶ N₀)
    (fStage gStage : (etaleNeighborhoodToSmooth X ξ).obj N₀ ⟶ Y)
    (hfStage : fStage = etaleNeighborhoodHom X ξ N₀ ≫ f₀)
    (hgStage : gStage = etaleNeighborhoodHom X ξ N₀ ≫ g₀)
    (hMaps : F.map ((etaleNeighborhoodToSmooth X ξ).map v ≫ fStage).op =
      F.map ((etaleNeighborhoodToSmooth X ξ).map v ≫ gStage).op) :
    F.map (etaleNeighborhoodHom X ξ N ≫ f₀).op =
      F.map (etaleNeighborhoodHom X ξ N ≫ g₀).op := by
  have hf : (etaleNeighborhoodToSmooth X ξ).map v ≫ fStage =
      etaleNeighborhoodHom X ξ N ≫ f₀ := by
    rw [hfStage, ← Category.assoc, etaleNeighborhoodMap_comp_hom ξ v]
  have hg : (etaleNeighborhoodToSmooth X ξ).map v ≫ gStage =
      etaleNeighborhoodHom X ξ N ≫ g₀ := by
    rw [hgStage, ← Category.assoc, etaleNeighborhoodMap_comp_hom ξ v]
  simpa only [hf, hg] using hMaps

namespace EtaleChart

/-- The actual S1 homomorphism equality supplies the representative equality
required by the existing induction step. The lower-dimensional iso is retained. -/
theorem exists_representative_preimage_of_restriction_maps_eq
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {A Y Z T : SmoothSite S} [IsAffine A.left] [IsAffine Y.left]
    [IsAffine Z.left] [IsAffine T.left]
    (q : A ⟶ Z) [Etale q.left] (p : Z ⟶ Y) (s : Y ⟶ Z) (g : Y ⟶ T)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Y.left)
    (ζ : Spec (.of Ω) ⟶ T.left)
    (hξ : ξ ≫ q.left = η ≫ s.left) (hs : s.left ≫ p.left = 𝟙 Y.left)
    (hg : η ≫ g.left = ζ) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    [IsIso (etaleNeighborhoodValuePullback g hg F)] (a : F.obj (op A))
    (N : EtaleNeighborhood (refinementObject q p s) (refinementMark q p s ξ η hξ hs))
    (hMaps : F.map (etaleNeighborhoodHom _ _ N ≫ refinementToChart q p s).op =
      F.map (etaleNeighborhoodHom _ _ N ≫
        (refinementToSection q p s ≫ sectionToChart q s)).op) :
    ∃ z : etaleNeighborhoodValue T ζ F,
      etaleNeighborhoodValuePullback ((q ≫ p) ≫ g) (by
        change ξ ≫ ((q ≫ p).left ≫ g.left) = ζ
        rw [← Category.assoc, chartMark_base q p s ξ η hξ hs, hg]) F z =
          toEtaleNeighborhoodValueFromObject A ξ F a := by
  exact exists_representative_preimage_of_restrictions_eq
    q p s g ξ η ζ hξ hs hg F a N (ConcreteCategory.congr_hom hMaps a)

/-- The terminal action on a refinement of the chosen stage is applied to the
original representative on that same final neighborhood. This proves only the
conditional induction step; its lower-dimensional isomorphism is not discharged. -/
theorem exists_representative_preimage_of_stage_restriction_maps_eq
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {A Y Z T : SmoothSite S} [IsAffine A.left] [IsAffine Y.left]
    [IsAffine Z.left] [IsAffine T.left]
    (q : A ⟶ Z) [Etale q.left] (p : Z ⟶ Y) (s : Y ⟶ Z) (g : Y ⟶ T)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Y.left)
    (ζ : Spec (.of Ω) ⟶ T.left)
    (hξ : ξ ≫ q.left = η ≫ s.left) (hs : s.left ≫ p.left = 𝟙 Y.left)
    (hg : η ≫ g.left = ζ) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    [IsIso (etaleNeighborhoodValuePullback g hg F)] (a : F.obj (op A))
    (N N₀ : EtaleNeighborhood (refinementObject q p s) (refinementMark q p s ξ η hξ hs))
    (v : N ⟶ N₀)
    (fStage gStage : (etaleNeighborhoodToSmooth _ _).obj N₀ ⟶ A)
    (hfStage : fStage = etaleNeighborhoodHom _ _ N₀ ≫ refinementToChart q p s)
    (hgStage : gStage = etaleNeighborhoodHom _ _ N₀ ≫
      (refinementToSection q p s ≫ sectionToChart q s))
    (hMaps : F.map ((etaleNeighborhoodToSmooth _ _).map v ≫ fStage).op =
      F.map ((etaleNeighborhoodToSmooth _ _).map v ≫ gStage).op) :
    ∃ z : etaleNeighborhoodValue T ζ F,
      etaleNeighborhoodValuePullback ((q ≫ p) ≫ g) (by
        change ξ ≫ ((q ≫ p).left ≫ g.left) = ζ
        rw [← Category.assoc, chartMark_base q p s ξ η hξ hs, hg]) F z =
          toEtaleNeighborhoodValueFromObject A ξ F a := by
  apply exists_representative_preimage_of_restriction_maps_eq
    q p s g ξ η ζ hξ hs hg F a N
  exact etaleNeighborhood_restriction_maps_eq_of_stage
    (refinementMark q p s ξ η hξ hs) F
    (refinementToChart q p s) (refinementToSection q p s ≫ sectionToChart q s)
    v fStage gStage hfStage hgStage hMaps

end EtaleChart
end AlgebraicGeometry.Scheme.SmoothSite
