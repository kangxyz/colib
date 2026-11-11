/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Cartesian constant sections of the native cylinder

Adapted from `Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/AffineLine/Complement.lean`
at motivic commit a6805c4a87cdfd7717dd7a94039246a167f15380,
blob 04e207934b1c046be1d982a37259855b97381acf.
The affine section is the existing `Contraction.nativeAffineSection`; its
comparison with literal polynomial evaluation is not a new affine-line model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Applying a map to the second parameter gives its literal scheme base change. -/
theorem productMap_right_isPullback {S : Scheme.{u}} (X : SmoothSite S)
    {U V : SmoothSite S} (j : U ⟶ V) :
    IsPullback (productMap (𝟙 X) j).left (productSnd X U).left
      (productSnd X V).left j.left := by
  apply IsPullback.of_right (h₁₂ := (productFst X V).left)
    (h₂₂ := V.hom) (v₁₃ := X.hom)
  · have hf := congrArg (fun f => f.left) (productMap_fst (𝟙 X) j)
    change (productMap (𝟙 X) j).left ≫ (productFst X V).left =
      (productFst X U).left ≫ 𝟙 X.left at hf
    rw [hf, Category.comp_id, MorphismProperty.Over.w]
    exact IsPullback.of_hasPullback X.hom U.hom
  · exact congrArg (fun f => f.left) (productMap_snd (𝟙 X) j)
  · exact IsPullback.of_hasPullback X.hom V.hom

/-- A constant relative section is the base change of the specified parameter point. -/
theorem productSection_isPullback {S : Scheme.{u}} (X T : SmoothSite S)
    (z : base S ⟶ T) :
    IsPullback (productLift (𝟙 X) (Contraction.toBase X ≫ z)).left X.hom
      (productSnd X T).left z.left := by
  apply IsPullback.of_right (h₁₂ := (productFst X T).left)
    (h₂₂ := T.hom) (v₁₃ := X.hom)
  · have hf := congrArg (fun f => f.left)
      (productLift_fst (𝟙 X) (Contraction.toBase X ≫ z))
    change (productLift (𝟙 X) (Contraction.toBase X ≫ z)).left ≫
      (productFst X T).left = 𝟙 X.left at hf
    rw [hf, MorphismProperty.Over.w]
    change IsPullback (𝟙 X.left) X.hom X.hom (𝟙 S)
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · exact congrArg (fun f => f.left)
      (productLift_snd (𝟙 X) (Contraction.toBase X ≫ z))
  · exact IsPullback.of_hasPullback X.hom T.hom

namespace Contraction

/-- The existing native affine section has its full Cartesian parameter square. -/
theorem nativeAffineSection_isPullback (R : CommRingCat.{u})
    (X : SmoothSite (Spec R)) (a : R) :
    IsPullback (nativeAffineSection R X a).left X.hom
      (productSnd X (additiveGroupObject (Spec R))).left
      ((polynomialAffinePoint R a ≫ (affineLinePolynomialIso R).inv).left) := by
  simpa only [nativeAffineSection, Category.assoc] using
    productSection_isPullback X (additiveGroupObject (Spec R))
      (polynomialAffinePoint R a ≫ (affineLinePolynomialIso R).inv)

/-- Literal polynomial evaluation is a closed point over the coefficient ring. -/
instance polynomialAffinePoint_isClosedImmersion (R : CommRingCat.{u}) (a : R) :
    IsClosedImmersion (polynomialAffinePoint R a).left :=
  IsClosedImmersion.spec_of_surjective _ (fun r => ⟨Polynomial.C r, by simp⟩)

/-- Each existing native constant section is a closed immersion, by actual base change. -/
instance nativeAffineSection_isClosedImmersion (R : CommRingCat.{u})
    (X : SmoothSite (Spec R)) (a : R) :
    IsClosedImmersion (nativeAffineSection R X a).left := by
  have : IsClosedImmersion
      (polynomialAffinePoint R a ≫ (affineLinePolynomialIso R).inv).left := by
    change IsClosedImmersion
      ((polynomialAffinePoint R a).left ≫ (affineLinePolynomialIso R).inv.left)
    infer_instance
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsClosedImmersion) (nativeAffineSection_isPullback R X a).flip inferInstance

end Contraction

end AlgebraicGeometry.Scheme.SmoothSite
