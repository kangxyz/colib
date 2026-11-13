/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison
public import Colib.AlgebraicGeometry.Sites.Smooth.Products.ProductPermutation

/-!
# Naturality of the original constant affine section in native coordinates

The existing section is unchanged; its literal product projections prove
naturality. This is the native-coordinate map used by the zero-section argument
in `Motivic/Cohomology/A1/LocalVanishing/Puncture/PointDiagrams.lean` at
`kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`, blob
`dd2775346278c19a5a32ed24c081c7cf0f451835`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.Contraction

/-- The literal native-coordinate constant section commutes with each original
smooth-site morphism, not merely with its isomorphism class. -/
@[reassoc]
theorem nativeAffineSection_naturality (R : CommRingCat.{u})
    {X Y : SmoothSite (Spec R)} (f : X ⟶ Y) (a : R) :
    nativeAffineSection R X a ≫ affineLineCylinder.map f =
      f ≫ nativeAffineSection R Y a := by
  let G := additiveGroupObject (Spec R)
  let c := polynomialAffinePoint R a ≫ (affineLinePolynomialIso R).inv
  let sX : X ⟶ product X G := productLift (𝟙 X) (toBase X ≫ c)
  let sY : Y ⟶ product Y G := productLift (𝟙 Y) (toBase Y ≫ c)
  let m := productMap f (𝟙 G)
  change sX ≫ m = f ≫ sY
  apply product_hom_ext (X := Y) (Y := G)
  · calc
      (sX ≫ m) ≫ productFst Y G = sX ≫ productFst X G ≫ f :=
        (Category.assoc sX m _).trans (congrArg (fun g => sX ≫ g) (productMap_fst f (𝟙 G)))
      _ = f := (productLift_fst_assoc (𝟙 X) (toBase X ≫ c) f).trans (Category.id_comp f)
      _ = (f ≫ sY) ≫ productFst Y G :=
        ((Category.assoc f sY _).trans
          ((congrArg (fun g => f ≫ g) (productLift_fst (𝟙 Y) (toBase Y ≫ c))).trans
            (Category.comp_id f))).symm
  · calc
      (sX ≫ m) ≫ productSnd Y G = sX ≫ productSnd X G :=
        (Category.assoc sX m _).trans
          (congrArg (fun g => sX ≫ g) ((productMap_snd f (𝟙 G)).trans (Category.comp_id _)))
      _ = toBase X ≫ c := productLift_snd (𝟙 X) (toBase X ≫ c)
      _ = f ≫ toBase Y ≫ c := (comp_toBase_assoc f c).symm
      _ = (f ≫ sY) ≫ productSnd Y G :=
        ((Category.assoc f sY _).trans
          (congrArg (fun g => f ≫ g) (productLift_snd (𝟙 Y) (toBase Y ≫ c)))).symm

/-- Moving the native affine parameter past a second factor preserves
its literal scalar section. -/
@[reassoc]
theorem productMap_nativeAffineSection_comp_productSwapLast
    (R : CommRingCat.{u}) (U D : SmoothSite (Spec R)) (a : R) :
    productMap (nativeAffineSection R U a) (𝟙 D) ≫
      productSwapLast U (additiveGroupObject (Spec R)) D =
    nativeAffineSection R (product U D) a := by
  let G := additiveGroupObject (Spec R)
  let c := polynomialAffinePoint R a ≫ (affineLinePolynomialIso R).inv
  let s : U ⟶ product U G := productLift (𝟙 U) (toBase U ≫ c)
  change productMap s (𝟙 D) ≫ productSwapLast U G D =
    productLift (𝟙 (product U D)) (toBase (product U D) ≫ c)
  apply product_hom_ext
  · rw [Category.assoc, productSwapLast_fst, ← productMap_comp, Category.id_comp]
    have hs : s ≫ productFst U G = 𝟙 U := productLift_fst _ _
    rw [hs, productMap_id, productLift_fst]
  · rw [Category.assoc, productSwapLast_snd, productMap_fst_assoc, productLift_snd,
      productLift_snd, comp_toBase_assoc]

end AlgebraicGeometry.Scheme.SmoothSite.Contraction
