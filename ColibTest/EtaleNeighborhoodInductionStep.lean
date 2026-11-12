/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodInductionStep

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
universe u

local instance {S : Scheme.{u}} [IsAffine S] : IsAffine (base S).left :=
  inferInstanceAs (IsAffine S)

/-- The source is the actual base marked-neighborhood value, not the value F(S). -/
example {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {A Y Z : SmoothSite S} [IsAffine A.left] [IsAffine Y.left]
    [IsAffine Z.left] [IsAffine S]
    (q : A ⟶ Z) [Etale q.left] (p : Z ⟶ Y) (s : Y ⟶ Z) (g : Y ⟶ (base S))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Y.left)
    (ζ : Spec (.of Ω) ⟶ (base S).left)
    (hξ : ξ ≫ q.left = η ≫ s.left) (hs : s.left ≫ p.left = 𝟙 Y.left)
    (hg : η ≫ g.left = ζ) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    [IsIso (etaleNeighborhoodValuePullback g hg F)] (a : F.obj (op A))
    (N : EtaleNeighborhood (refinementObject q p s) (refinementMark q p s ξ η hξ hs))
    (ha : (F.map (etaleNeighborhoodHom _ _ N ≫ refinementToChart q p s).op).hom a =
      (F.map (etaleNeighborhoodHom _ _ N ≫
        (refinementToSection q p s ≫ sectionToChart q s)).op).hom a) :
    ∃ z : etaleNeighborhoodValue (base S) ζ F,
      etaleNeighborhoodValuePullback ((q ≫ p) ≫ g) (by
        change ξ ≫ ((q ≫ p).left ≫ g.left) = ζ
        rw [← Category.assoc, chartMark_base q p s ξ η hξ hs, hg]) F z =
          toEtaleNeighborhoodValueFromObject A ξ F a :=
  exists_representative_preimage_of_restrictions_eq q p s g ξ η ζ hξ hs hg F a N ha
