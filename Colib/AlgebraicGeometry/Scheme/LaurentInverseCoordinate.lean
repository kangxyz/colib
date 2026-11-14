/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.LaurentCoordinateNaturality
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentProjection

/-! # The inverse Laurent chart sends the coordinate to the inverse unit -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

/-- On the actual inverse chart, the polynomial section restricts to the section `T⁻¹`. -/
theorem laurentMinus_appTop_coordinate (R : CommRingCat.{u}) :
    (laurentMinus R).appTop (polynomialCoordinate R) = ↑((laurentCoordinate R)⁻¹) := by
  rw [laurentCoordinate_inv_val]
  let f : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R) :=
    CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)
  have h := (ConcreteCategory.congr_hom (ΓSpecIso_inv_naturality f) Polynomial.X).symm
  change (Spec.map f).appTop.hom ((ΓSpecIso (.of (Polynomial R))).inv.hom Polynomial.X) =
    (ΓSpecIso (.of (LaurentPolynomial R))).inv.hom (f.hom Polynomial.X) at h
  change (Spec.map f).appTop.hom ((ΓSpecIso (.of (Polynomial R))).inv.hom Polynomial.X) = _
  rw [h]
  congr 1
  change LaurentPolynomial.invert (Polynomial.toLaurent Polynomial.X) = _
  rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T]

end AlgebraicGeometry.Scheme.PolynomialLaurent
