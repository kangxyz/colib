/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Etale.AffineSpaceInduction
import Colib.AlgebraicGeometry.Sites.Smooth.Etale.StrictHenselization
import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.SmoothSite

noncomputable section

universe u

section BaseChange

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]
  {X Y Z : Scheme.SmoothSite S} [IsAffine X.left] [IsAffine Y.left] [IsAffine Z.left]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  {ξ : Spec (.of Ω) ⟶ X.left} {η : Spec (.of Ω) ⟶ Y.left}
  {ζ : Spec (.of Ω) ⟶ Z.left}
  (F : (Scheme.SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

example (f : X ⟶ Y) (h : ξ ≫ f.left = η) (B : EtaleNeighborhood Y η) :
    IsPullback (etaleNeighborhoodHom X ξ (etaleNeighborhoodPullback f h B)).left
      (etaleNeighborhoodPullbackHom f h B).left f.left (etaleNeighborhoodHom Y η B).left :=
  etaleNeighborhoodPullback_isPullback f h B

example (f : X ⟶ Y) (h : ξ ≫ f.left = η) (B : EtaleNeighborhood Y η) :
    etaleNeighborhoodMark X ξ (etaleNeighborhoodPullback f h B) ≫
      (etaleNeighborhoodPullbackHom f h B).left = etaleNeighborhoodMark Y η B :=
  etaleNeighborhoodPullbackMark_hom f h B

example (f : X ⟶ Y) (h : ξ ≫ f.left = η) (B : EtaleNeighborhood Y η)
    (b : F.obj (op ((etaleNeighborhoodToSmooth Y η).obj B))) :
    etaleNeighborhoodValuePullback f h F (toEtaleNeighborhoodValue Y η B F b) =
      toEtaleNeighborhoodValue X ξ (etaleNeighborhoodPullback f h B) F
        (F.map (etaleNeighborhoodPullbackHom f h B).op b) :=
  ConcreteCategory.congr_hom (toEtaleNeighborhoodValue_pullback f h F B) b

example : etaleNeighborhoodValuePullback (𝟙 X) (ξ := ξ) (by simp) F = 𝟙 _ :=
  etaleNeighborhoodValuePullback_id F

example (f : X ⟶ Y) (g : Y ⟶ Z) (hf : ξ ≫ f.left = η) (hg : η ≫ g.left = ζ) :
    etaleNeighborhoodValuePullback (f ≫ g) (by
      change ξ ≫ (f.left ≫ g.left) = ζ
      rw [← Category.assoc, hf, hg]) F =
      etaleNeighborhoodValuePullback g hg F ≫ etaleNeighborhoodValuePullback f hf F :=
  etaleNeighborhoodValuePullback_comp f g hf hg F

example (p : X ⟶ Y) (s : Y ⟶ X) (hp : ξ ≫ p.left = η) (hs : η ≫ s.left = ξ)
    (hsp : s ≫ p = 𝟙 Y) :
    etaleNeighborhoodValuePullback p hp F ≫ etaleNeighborhoodValuePullback s hs F = 𝟙 _ :=
  etaleNeighborhoodValuePullback_retraction p s hp hs hsp F

end BaseChange

section AffineSpace

variable (k : Type u) [Field k] (d : ℕ)
  (F : (Scheme.SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

example : (affineSpaceOriginGeometricPoint k d).residueField = AlgebraicClosure k := rfl

example : (affineSpaceOriginGeometricPoint k d).hom =
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫ affineSpaceOrigin k d := rfl

example : affineSpaceCoordinateZeroSection k d ≫ affineSpaceCoordinateProjection k d = 𝟙 _ :=
  affineSpaceCoordinateZeroSection_projection k d

example : affineSpaceOriginProjectionPullback k d F ≫
    affineSpaceOriginZeroSectionPullback k d F = 𝟙 _ :=
  affineSpaceOriginProjectionPullback_zeroSection k d F

example (a : affineSpaceOriginValue k d F) :
    affineSpaceOriginZeroSectionPullback k d F (affineSpaceOriginProjectionPullback k d F a) = a :=
  ConcreteCategory.congr_hom (affineSpaceOriginProjectionPullback_zeroSection k d F) a

example : affineSpaceOriginValue k d F =
    etaleNeighborhoodValue (affineSpaceObject k d) (affineSpaceOriginGeometricPoint k d).hom F := rfl

example (B : BigEtaleSite.{u}) (hX : B.Contains (affineSpaceObject k d).left) :
    IsLimit (etaleNeighborhoodStrictHenselizationCone (affineSpaceObject k d) B hX
      (affineSpaceOriginGeometricPoint k d)) :=
  etaleNeighborhoodStrictHenselizationConeIsLimit _ _ _ _

example (B : BigEtaleSite.{u}) (hX : B.Contains (affineSpaceObject k d).left)
    (A : EtaleNeighborhood (affineSpaceObject k d) (affineSpaceOriginGeometricPoint k d).hom) :
    geometricPointToStrictHenselization B (affineSpaceObject k d).left hX
        (affineSpaceOriginGeometricPoint k d) ≫
      (etaleNeighborhoodStrictHenselizationCone (affineSpaceObject k d) B hX
        (affineSpaceOriginGeometricPoint k d)).π.app A =
      etaleNeighborhoodMark (affineSpaceObject k d) (affineSpaceOriginGeometricPoint k d).hom A :=
  geometricPointToStrictHenselization_comp_etaleNeighborhoodCone_π _ _ _ _ _

end AffineSpace

section Transfers

variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)

example (d : ℕ) :
    affineSpaceOriginProjectionPullback k d ((PresheafWithTransfers.toPresheaf k).obj P) ≫
      affineSpaceOriginZeroSectionPullback k d ((PresheafWithTransfers.toPresheaf k).obj P) = 𝟙 _ :=
  affineSpaceOriginProjectionPullback_zeroSection k d _

example {X Y : Scheme.SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {ξ : Spec (.of Ω) ⟶ X.left} {η : Spec (.of Ω) ⟶ Y.left}
    (f : X ⟶ Y) (h : ξ ≫ f.left = η) (B : EtaleNeighborhood Y η) :
    toEtaleNeighborhoodValue Y η B ((PresheafWithTransfers.toPresheaf k).obj P) ≫
        etaleNeighborhoodValuePullback f h ((PresheafWithTransfers.toPresheaf k).obj P) =
      PresheafWithTransfers.transfer P
        ((Cor.graphFunctor k).map (etaleNeighborhoodPullbackHom f h B)) ≫
          toEtaleNeighborhoodValue X ξ (etaleNeighborhoodPullback f h B)
            ((PresheafWithTransfers.toPresheaf k).obj P) :=
  toEtaleNeighborhoodValue_pullback f h _ B

end Transfers

#print axioms etaleNeighborhoodPullback
#print axioms etaleNeighborhoodPullback_isPullback
#print axioms etaleNeighborhoodValuePullback
#print axioms toEtaleNeighborhoodValue_pullback_of_compatible
#print axioms etaleNeighborhoodValuePullback_id
#print axioms etaleNeighborhoodValuePullback_comp
#print axioms etaleNeighborhoodValuePullback_retraction
#print axioms affineSpaceOriginGeometricPoint
#print axioms affineSpaceCoordinateZeroSection_projection
#print axioms affineSpaceOriginGeometricPoint_projection
#print axioms affineSpaceOriginGeometricPoint_zeroSection
#print axioms affineSpaceOriginProjectionPullback_zeroSection

end
