/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Polynomial.Laurent

/-! # Native affine polynomial and Laurent coordinates

The map is `Spec.map Polynomial.toLaurent` on the actual native polynomial and Laurent
rings. The sections are the images of `X` and the forward unit `T 1` under `ΓSpecIso`.
This makes the affine specialization of the scalar comparison explicit without introducing
another affine-line or Laurent-scheme model.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.PolynomialLaurent

universe u
variable (R : CommRingCat.{u})

/-- The actual affine positive Laurent open. -/
def laurentToPolynomial : Spec (.of (LaurentPolynomial R)) ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent)

instance : IsOpenImmersion (laurentToPolynomial R) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial R)

/-- The native polynomial coordinate, as a section of its actual affine spectrum. -/
def polynomialCoordinate : Γ(Spec (.of (Polynomial R)), ⊤) :=
  (ΓSpecIso (.of (Polynomial R))).inv.hom Polynomial.X

/-- The forward Laurent coordinate is the image of the actual unit `T 1`. -/
def laurentCoordinate : (Γ(Spec (.of (LaurentPolynomial R)), ⊤))ˣ :=
  ((LaurentPolynomial.isUnit_T (R := R) 1).map
    (ΓSpecIso (.of (LaurentPolynomial R))).inv.hom).unit

/-- The actual affine open map takes `X` to the forward Laurent unit, with no inversion. -/
theorem laurentToPolynomial_appTop_coordinate :
    (laurentToPolynomial R).appTop (polynomialCoordinate R) = (laurentCoordinate R).val := by
  have h := ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R))
  have hX := congrArg (fun f => f.hom Polynomial.X) h
  change (ΓSpecIso (.of (LaurentPolynomial R))).inv.hom (Polynomial.toLaurent Polynomial.X) =
    (Spec.map (CommRingCat.ofHom Polynomial.toLaurent)).appTop.hom
      ((ΓSpecIso (.of (Polynomial R))).inv.hom Polynomial.X) at hX
  simpa only [Polynomial.toLaurent_X, laurentToPolynomial, polynomialCoordinate,
    laurentCoordinate, IsUnit.unit_spec] using hX.symm

end AlgebraicGeometry.Scheme.PolynomialLaurent
