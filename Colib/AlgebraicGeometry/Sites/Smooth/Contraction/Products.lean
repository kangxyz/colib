/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry

/-!
# Actual base-product and factor-exchange comparisons

These isomorphisms retain the literal relative products and their projections.
They are the geometric comparison maps used by the transfer-natural unit split.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.Contraction

variable {S : Scheme.{u}}

/-- The literal product with the base has the first projection as its comparison. -/
def productBaseIso (X : SmoothSite S) : product X (base S) ≅ X where
  hom := productFst X (base S)
  inv := productLift (𝟙 X) (toBase X)
  hom_inv_id := by
    apply product_hom_ext
    · simp
    · simp only [Category.assoc, productLift_snd, Category.id_comp]
      apply MorphismProperty.Over.Hom.ext
      change pullback.fst X.hom (𝟙 S) ≫ X.hom = pullback.snd X.hom (𝟙 S)
      simpa using pullback.condition (f := X.hom) (g := 𝟙 S)
  inv_hom_id := productLift_fst _ _

/-- The actual parameter structural map gives exactly the first projection. -/
@[reassoc (attr := simp)]
theorem productMap_toBase (X T : SmoothSite S) :
    productMap (𝟙 X) (toBase T) ≫ (productBaseIso X).hom = productFst X T := by
  simp [productBaseIso]

/-- The actual base-coordinate unit becomes the existing native unit section. -/
@[reassoc (attr := simp)]
theorem baseProduct_unit (X : SmoothSite S) :
    (productBaseIso X).inv ≫ productMap (𝟙 X) (torusOne S) = unitSection.app X := by
  apply product_hom_ext <;> simp [productBaseIso, unitSection]

/-- Exchange the last two factors of the actual relative triple product. -/
def productSwapRight (X Y Z : SmoothSite S) :
    product (product X Y) Z ≅ product (product X Z) Y where
  hom := productLift
    (productLift (productFst (product X Y) Z ≫ productFst X Y)
      (productSnd (product X Y) Z))
    (productFst (product X Y) Z ≫ productSnd X Y)
  inv := productLift
    (productLift (productFst (product X Z) Y ≫ productFst X Z)
      (productSnd (product X Z) Y))
    (productFst (product X Z) Y ≫ productSnd X Z)
  hom_inv_id := by
    apply product_hom_ext
    · apply product_hom_ext <;> simp
    · simp
  inv_hom_id := by
    apply product_hom_ext
    · apply product_hom_ext <;> simp
    · simp

/-- The exchange identifies precisely the projections dropping the middle factor. -/
@[reassoc (attr := simp)]
theorem productSwapRight_hom_fst (X Y Z : SmoothSite S) :
    (productSwapRight X Y Z).hom ≫ productFst (product X Z) Y =
      productMap (productFst X Y) (𝟙 Z) := by
  apply product_hom_ext <;> simp [productSwapRight]

end AlgebraicGeometry.Scheme.SmoothSite.Contraction
