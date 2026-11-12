/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison

/-! # Naturality of the native affine-cylinder polynomial comparison

Both arrows below are products of the actual parameter isomorphism with the
identity. No alternate active cylinder or naturality provider is introduced.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.Contraction

/-- The inverse parameter comparison preserves the literal projection. -/
@[reassoc (attr := simp)] theorem affineCylinderPolynomialIso_inv_projection
    (R : CommRingCat.{u}) (X : SmoothSite (Spec R)) :
    (affineCylinderPolynomialIso R X).inv ≫
        (projection (additiveGroupObject (Spec R))).app X =
      productFst X (polynomialAffineLine R) := by
  rw [← affineCylinderPolynomialIso_hom_projection R X]
  exact Iso.inv_hom_id_assoc _ _

/-- The inverse native comparison commutes with every original base morphism. -/
@[reassoc] theorem affineCylinderPolynomialIso_inv_naturality
    (R : CommRingCat.{u}) {X Y : SmoothSite (Spec R)} (f : X ⟶ Y) :
    productMap f (𝟙 (polynomialAffineLine R)) ≫
        (affineCylinderPolynomialIso R Y).inv =
      (affineCylinderPolynomialIso R X).inv ≫ affineLineCylinder.map f := by
  change productMap f (𝟙 (polynomialAffineLine R)) ≫
      productMap (𝟙 Y) (affineLinePolynomialIso R).inv =
    productMap (𝟙 X) (affineLinePolynomialIso R).inv ≫
      productMap f (𝟙 (additiveGroupObject (Spec R)))
  rw [← productMap_comp, ← productMap_comp]
  simp

end AlgebraicGeometry.Scheme.SmoothSite.Contraction
