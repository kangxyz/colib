/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Products.ProductPermutation
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/Boundary/Contraction/ProjectionGeometry.lean`,
blob `700588ec732369a67646a9cb624b66632b4a45be`.
Only the independent parameter-permutation identities are extracted, for the
existing native additive and multiplicative parameters and native constant section.
Source candidate only; no elaboration result is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
open Contraction
variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))

/-- The actual Laurent puncture commutes with parameter permutation. -/
theorem contractionOpen_productSwapLast :
    openInclusion.app (affineLineCylinder.obj X) ≫
        productSwapLast X (additiveGroupObject (Spec R)) (additiveGroupObject (Spec R)) =
      productSwapLast X (additiveGroupObject (Spec R)) (multiplicativeGroupObject (Spec R)) ≫
        affineLineCylinder.map (openInclusion.app X) := by
  let T := additiveGroupObject (Spec R)
  let M := multiplicativeGroupObject (Spec R)
  let j := multiplicativeGroupOpen (Spec R)
  change productMap (𝟙 (product X T)) j ≫ productSwapLast X T T =
    productSwapLast X T M ≫ productMap (productMap (𝟙 X) j) (𝟙 T)
  simpa only [productMap_id] using
    productSwapLast_naturality X (additiveGroupObject (Spec R))
      (multiplicativeGroupObject (Spec R)) (𝟙 X) (𝟙 (additiveGroupObject (Spec R)))
      (multiplicativeGroupOpen (Spec R))

/-- Forgetting the permuted parameter retains the original punctured projection. -/
theorem torusProjection_productSwapLast :
    productSwapLast X (additiveGroupObject (Spec R)) (multiplicativeGroupObject (Spec R)) ≫
        (projection (additiveGroupObject (Spec R))).app (torusCylinder.obj X) =
      productMap ((projection (additiveGroupObject (Spec R))).app X)
        (𝟙 (multiplicativeGroupObject (Spec R))) :=
  productSwapLast_fst X (additiveGroupObject (Spec R)) (multiplicativeGroupObject (Spec R))

/-- Forgetting the permuted parameter retains the original ambient projection. -/
theorem a1Projection_productSwapLast :
    productSwapLast X (additiveGroupObject (Spec R)) (additiveGroupObject (Spec R)) ≫
        (projection (additiveGroupObject (Spec R))).app (affineLineCylinder.obj X) =
      affineLineCylinder.map ((projection (additiveGroupObject (Spec R))).app X) :=
  productSwapLast_fst X (additiveGroupObject (Spec R)) (additiveGroupObject (Spec R))

/-- The entire native constant section, not just its point, is preserved by permutation. -/
theorem a1Section_productSwapLast (a : R) :
    nativeAffineSection R (affineLineCylinder.obj X) a ≫
        productSwapLast X (additiveGroupObject (Spec R)) (additiveGroupObject (Spec R)) =
      affineLineCylinder.map (nativeAffineSection R X a) := by
  let T := additiveGroupObject (Spec R)
  let c := polynomialAffinePoint R a ≫ (affineLinePolynomialIso R).inv
  change productLift (𝟙 (product X T)) (toBase (product X T) ≫ c) ≫
      productSwapLast X T T =
    productMap (productLift (𝟙 X) (toBase X ≫ c)) (𝟙 T)
  apply product_hom_ext
  · rw [Category.assoc, productSwapLast_fst, productMap_fst]
    apply product_hom_ext
    · simp only [Category.assoc, productMap_fst]
      rw [productLift_fst_assoc, Category.id_comp, productLift_fst, Category.comp_id]
    · simp [Category.assoc]
  · rw [Category.assoc, productSwapLast_snd, productMap_snd]
    simp only [Category.comp_id]
    rw [productLift_fst_assoc, Category.id_comp]

end AlgebraicGeometry.Scheme.SmoothSite
