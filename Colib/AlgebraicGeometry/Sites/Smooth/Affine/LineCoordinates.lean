/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.Coordinates
public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.OpenMaps
public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.Ambient
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.PolynomialNaturality

/-! # Actual affine-cylinder coordinates with the native additive parameter -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Affine/LineCoordinates.lean`, blob
`bf509ca62bbe2f68a50e37eb76aa093558f1c00b`.
The active affine cylinder remains the existing native additive group object.
The polynomial spectrum is only an explicit comparison target.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- The literal polynomial spectrum is the product with the comparison parameter. -/
def linePolynomialProductIso : lineSite (k := k) (R := R) ≅
    product (affineSite k R) (polynomialAffineLine (.of k)) :=
  MorphismProperty.Over.isoMk (ambientIso (algebraMap k R)) (by
    change (ambientIso (algebraMap k R)).hom ≫
      (pullback.fst _ _ ≫ _) = _
    rw [← Category.assoc, ambientIso_fst]
    rfl)

@[reassoc (attr := simp)] theorem linePolynomialProductIso_projection :
    (linePolynomialProductIso (k := k) (R := R)).hom ≫
      productFst (affineSite k R) (polynomialAffineLine (.of k)) =
      homMk (polynomialProjection (.of R)) rfl := by
  apply MorphismProperty.Over.Hom.ext
  exact ambientIso_fst (algebraMap k R)

/-- The polynomial product is compared to the unchanged native additive cylinder. -/
def lineCylinderIso : lineSite (k := k) (R := R) ≅
    affineLineCylinder.obj (affineSite k R) :=
  linePolynomialProductIso ≪≫ (affineCylinderPolynomialIso (.of k) (affineSite k R)).symm

@[reassoc (attr := simp)] theorem lineCylinderIso_projection :
    (lineCylinderIso (k := k) (R := R)).hom ≫
      (projection (additiveGroupObject (Spec (.of k)))).app (affineSite k R) =
      homMk (polynomialProjection (.of R)) rfl := by
  simp only [lineCylinderIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    affineCylinderPolynomialIso_inv_projection, linePolynomialProductIso_projection]

/-- The actual native cylinder functor carries a site isomorphism to an isomorphism. -/
def cylinderIso {X Y : SmoothSite (Spec (.of k))} (e : X ≅ Y) :
    affineLineCylinder.obj X ≅ affineLineCylinder.obj Y :=
  affineLineCylinder.mapIso e

attribute [local instance] sectionsAlgebra

/-- Canonical global sections compare to the original affine object's native cylinder. -/
def affineLineIso (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    lineSite (k := k) (R := Γ(X.left, ⊤)) ≅ affineLineCylinder.obj X :=
  lineCylinderIso ≪≫ cylinderIso (affineIso X)

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
