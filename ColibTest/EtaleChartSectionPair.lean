/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodCurveSections
import Colib.AlgebraicGeometry.Polynomial.ValueSection
import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers
universe u

namespace EtaleChartRepresentativeTest
open AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
variable {k : Type u} [Field k]
  {A Y Z : SmoothSite (Spec (.of k))}
  [IsAffine A.left] [IsAffine Y.left] [IsAffine Z.left]
  (q : A ⟶ Z) [Etale q.left] (p : Z ⟶ Y) (s : Y ⟶ Z)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Y.left)
  (hξ : ξ ≫ q.left = η ≫ s.left) (hs : s.left ≫ p.left = 𝟙 Y.left)

/-- The restriction formula uses the original PST over k, even for extension-field stages. -/
example (P : PresheafWithTransfers.{u + 1} k) :
    ((toPresheaf k).obj P).map (sectionToChart q s).op ≫
      toEtaleNeighborhoodValueFromObject (sectionObject q s) (sectionMark q s ξ η hξ) ((toPresheaf k).obj P) ≫
      (etaleNeighborhoodValueEtaleIso (sectionToBase q s)
        (sectionMark_base q s ξ η hξ) ((toPresheaf k).obj P)).inv ≫
      etaleNeighborhoodValuePullback (q ≫ p)
        (chartMark_base q p s ξ η hξ hs) ((toPresheaf k).obj P) =
    ((toPresheaf k).obj P).map (refinementToSection q p s ≫ sectionToChart q s).op ≫
      toEtaleNeighborhoodValueFromObject (refinementObject q p s)
        (refinementMark q p s ξ η hξ hs) ((toPresheaf k).obj P) ≫
      (refinementValueIso q p s ξ η hξ hs ((toPresheaf k).obj P)).inv :=
  retract_representative q p s ξ η hξ hs ((toPresheaf k).obj P)
end EtaleChartRepresentativeTest

/-- Rational-value sections preserve an arbitrary original extension-field marking. -/
example (E Ω R : Type u) [Field E] [Field Ω] [Algebra E Ω]
    [CommRing R] [Algebra E R] (φ : Polynomial R →ₐ[E] E) :
    Spec.map (CommRingCat.ofHom (algebraMap E Ω)) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) =
    (Spec.map (CommRingCat.ofHom (algebraMap E Ω)) ≫
      Spec.map (CommRingCat.ofHom (φ.toRingHom.comp Polynomial.C))) ≫
        polynomialValueSection R (algebraMap E R (φ Polynomial.X)) := by
  rw [polynomialPoint_factors_valueSection E R φ, Category.assoc]

namespace EtaleChartResidueTest
open AlgebraicGeometry.Scheme.EtaleChart
variable {A Y Z U : Scheme.{u}} (q : A ⟶ Z) (p : Z ⟶ Y) (s : Y ⟶ Z)
  {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ A) (η : Spec (.of Ω) ⟶ Y)
  (hξ : ξ ≫ q = η ≫ s) (i : A ⟶ U) (f : U ⟶ Y) (hi : i ≫ f = q ≫ p)

example (hs : s ≫ p = 𝟙 Y) :
    (refinement q p s).fromSpecResidueField
        (refinementMark q p s ξ η hξ hs (IsLocalRing.closedPoint Ω)) ≫
      originalSection q p s i f hi =
    (refinement q p s).fromSpecResidueField
        (refinementMark q p s ξ η hξ hs (IsLocalRing.closedPoint Ω)) ≫
      retractSection q p s i f hi hs :=
  sections_same_residueField q p s ξ η hξ i f hi hs
end EtaleChartResidueTest
