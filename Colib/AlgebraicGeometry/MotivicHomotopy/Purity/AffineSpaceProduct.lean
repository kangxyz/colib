/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineSpaceZero
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartesian

/-! # The marked product of affine space with its base -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AffineSpace

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

/-- The projection of the literal affine space in the smooth site. -/
def affineSpaceProjection (X : SmoothSite S) (n : ℕ) : relativeAffineSpace X n ⟶ X :=
  homMk (AffineSpace (ULift.{u} (Fin n)) X.left ↘ X.left) rfl

/-- The zero section is a section of the original affine-space projection. -/
@[reassoc (attr := simp)]
theorem relativeAffineSpaceZeroSection_projection (X : SmoothSite S) (n : ℕ) :
    relativeAffineSpaceZeroSection X n ≫ affineSpaceProjection X n = 𝟙 X :=
  MorphismProperty.Over.Hom.ext (AffineSpace.origin_over _ _)

/-- The original product with the base in its first coordinate. -/
def baseProductLeftIso (X : SmoothSite S) : product (base S) X ≅ X where
  hom := productSnd (base S) X
  inv := productLift (Contraction.toBase X) (𝟙 X)
  hom_inv_id := by
    apply product_hom_ext
    · simp only [Category.assoc, productLift_fst, Category.id_comp]
      apply (baseIsTerminal S).hom_ext
    · simp
  inv_hom_id := productLift_snd _ _

/-- Formation of the native affine space is the indicated scheme pullback. -/
theorem affineSpaceProduct_isPullback (X : SmoothSite S) (n : ℕ) :
    IsPullback (affineSpaceObjectMap (Contraction.toBase X) n).left
      (affineSpaceProjection X n).left (relativeAffineSpace (base S) n).hom X.hom := by
  change IsPullback (AffineSpace.map (ULift.{u} (Fin n)) X.hom)
    (AffineSpace (ULift.{u} (Fin n)) X.left ↘ X.left)
    ((AffineSpace (ULift.{u} (Fin n)) S ↘ S) ≫ 𝟙 S) X.hom
  rw [Category.comp_id]
  exact AffineSpace.isPullback_map _

/-- The original change of base of affine space, with its two specified projections. -/
def affineSpaceProductIso (X : SmoothSite S) (n : ℕ) :
    relativeAffineSpace X n ≅ product (relativeAffineSpace (base S) n) X := by
  let e := (affineSpaceProduct_isPullback X n).isoPullback
  refine MorphismProperty.Over.isoMk e ?_
  change e.hom ≫ pullback.fst _ _ ≫ (relativeAffineSpace (base S) n).hom = _
  rw [← Category.assoc, IsPullback.isoPullback_hom_fst]
  exact MorphismProperty.Over.w (affineSpaceObjectMap (Contraction.toBase X) n)

@[reassoc (attr := simp)]
theorem affineSpaceProductIso_hom_fst (X : SmoothSite S) (n : ℕ) :
    (affineSpaceProductIso X n).hom ≫ productFst (relativeAffineSpace (base S) n) X =
      affineSpaceObjectMap (Contraction.toBase X) n :=
  MorphismProperty.Over.Hom.ext ((affineSpaceProduct_isPullback X n).isoPullback_hom_fst)

@[reassoc (attr := simp)]
theorem affineSpaceProductIso_hom_snd (X : SmoothSite S) (n : ℕ) :
    (affineSpaceProductIso X n).hom ≫ productSnd (relativeAffineSpace (base S) n) X =
      affineSpaceProjection X n :=
  MorphismProperty.Over.Hom.ext ((affineSpaceProduct_isPullback X n).isoPullback_hom_snd)

/-- This product comparison takes the origin to the original product zero section. -/
theorem affineSpaceProductIso_origin (X : SmoothSite S) (n : ℕ) :
    relativeAffineSpaceZeroSection X n ≫ (affineSpaceProductIso X n).hom =
      (baseProductLeftIso X).inv ≫
        productMap (relativeAffineSpaceZeroSection (base S) n) (𝟙 X) := by
  apply product_hom_ext
  · simp only [Category.assoc, affineSpaceProductIso_hom_fst, productMap_fst]
    change relativeAffineSpaceZeroSection X n ≫ affineSpaceObjectMap (Contraction.toBase X) n =
      productLift (Contraction.toBase X) (𝟙 X) ≫
        productFst (base S) X ≫ relativeAffineSpaceZeroSection (base S) n
    rw [productLift_fst_assoc]
    exact MorphismProperty.Over.Hom.ext (AffineSpace.origin_map X.left X.hom _)
  · simp only [Category.assoc, affineSpaceProductIso_hom_snd, productMap_snd, Category.comp_id,
      relativeAffineSpaceZeroSection_projection]
    exact (productLift_snd (Contraction.toBase X) (𝟙 X)).symm

end AlgebraicGeometry.Scheme.SmoothSite
