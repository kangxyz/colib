/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodInductionAction
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.StrictHenselization

/-! # The actual small-stage restriction output acts on the original representative

The terminal neighborhood remains the original Anew and its map v to the stage
selected by descent. The map of that stage to the fixed stage is composed using
the genuine small-neighborhood inclusion. No terminal stage is substituted and
no lower-dimensional pullback isomorphism is proved or assumed implicitly.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The actual small-stage transition composes to the original neighborhood map. -/
theorem smallEtaleNeighborhoodMap_comp_hom
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S) [IsAffine X.left]
    (s : GeometricPoint X.left) {i j : SmallEtaleNeighborhood X s} (v : i ⟶ j) :
    (smallEtaleNeighborhoodToSmooth X s).map v ≫
        etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj j) =
      etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i) :=
  etaleNeighborhoodMap_comp_hom s.hom ((smallEtaleNeighborhoodInclusion X s).map v)

namespace EtaleChart

/-- The geometric point of the actual refinement object is the original marking. -/
abbrev refinementGeometricPoint
    {S : Scheme.{u}} {A Y Z : SmoothSite S}
    [IsAffine A.left] [IsAffine Y.left] [IsAffine Z.left]
    (q : A ⟶ Z) [Etale q.left] (p : Z ⟶ Y) (s : Y ⟶ Z)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Y.left)
    (hξ : ξ ≫ q.left = η ≫ s.left) (hs : s.left ≫ p.left = 𝟙 Y.left) :
    GeometricPoint (refinementObject q p s).left where
  residueField := Ω
  hom := refinementMark q p s ξ η hξ hs

/-- The exact output shape of the actual fixed-target restriction producer,
with its original two fixed maps, supplies a preimage of the original a.
The explicitly supplied lower-dimensional IsIso remains the induction input. -/
theorem exists_representative_preimage_of_small_stage_restriction
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {A Y Z T : SmoothSite S} [IsAffine A.left] [IsAffine Y.left]
    [IsAffine Z.left] [IsAffine T.left]
    (q : A ⟶ Z) [Etale q.left] (p : Z ⟶ Y) (s : Y ⟶ Z) (g : Y ⟶ T)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Y.left)
    (ζ : Spec (.of Ω) ⟶ T.left)
    (hξ : ξ ≫ q.left = η ≫ s.left) (hs : s.left ≫ p.left = 𝟙 Y.left)
    (hg : η ≫ g.left = ζ) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    [IsIso (etaleNeighborhoodValuePullback g hg F)] (a : F.obj (op A))
    (i : SmallEtaleNeighborhood (refinementObject q p s)
      (refinementGeometricPoint q p s ξ η hξ hs))
    (hOutput :
      let X := refinementObject q p s
      let sRef := refinementGeometricPoint q p s ξ η hξ hs
      let fixedHom := etaleNeighborhoodHom X sRef.hom
        ((smallEtaleNeighborhoodInclusion X sRef).obj i)
      let f₀ := fixedHom ≫ refinementToChart q p s
      let g₀ := fixedHom ≫ (refinementToSection q p s ≫ sectionToChart q s)
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
          toEtaleNeighborhoodValueFromObject A ξ F a := by
  obtain ⟨ℓ, Anew, v, hMaps⟩ := hOutput
  apply exists_representative_preimage_of_stage_restriction_maps_eq
    q p s g ξ η ζ hξ hs hg F a Anew
    ((smallEtaleNeighborhoodInclusion (refinementObject q p s)
      (refinementGeometricPoint q p s ξ η hξ hs)).obj ℓ.left) v
    ((smallEtaleNeighborhoodToSmooth (refinementObject q p s)
      (refinementGeometricPoint q p s ξ η hξ hs)).map ℓ.hom ≫
      (etaleNeighborhoodHom _ _ ((smallEtaleNeighborhoodInclusion _ _).obj i) ≫
        refinementToChart q p s))
    ((smallEtaleNeighborhoodToSmooth (refinementObject q p s)
      (refinementGeometricPoint q p s ξ η hξ hs)).map ℓ.hom ≫
      (etaleNeighborhoodHom _ _ ((smallEtaleNeighborhoodInclusion _ _).obj i) ≫
        (refinementToSection q p s ≫ sectionToChart q s)))
  · rw [← Category.assoc, smallEtaleNeighborhoodMap_comp_hom]
  · rw [← Category.assoc, smallEtaleNeighborhoodMap_comp_hom]
  · exact hMaps

end EtaleChart
end AlgebraicGeometry.Scheme.SmoothSite
