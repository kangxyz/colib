/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarUnitComparison
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurent

/-! # The forward scalar comparison on actual affine polynomial spectra

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarLaurentClassComparison.lean:85-107`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Both spectra, their sections and the
positive Laurent open use native Mathlib objects and the actual `ΓSpecIso` maps.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

open PolynomialLaurent

universe u

/-- The forward polynomial coordinate restricts to the actual affine Laurent-unit class. -/
theorem polynomialScalarForwardKOneClass_restrict (R : CommRingCat.{u})
    (K : ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := (Spec (.of (Polynomial R))).toRingedSpace))) :
    perfectOpenKRestrict (laurentToPolynomial R) 1
        (perfectScalarForwardKOneClass (laurentToPolynomial R) K
          (polynomialCoordinate R) (laurentCoordinate R)
          (laurentToPolynomial_appTop_coordinate R)) =
      perfectGlobalUnitKOneClass _ (laurentCoordinate R)
        ((perfectComplexesRestrictOpenImmersion (laurentToPolynomial R)).obj K) :=
  perfectScalarForwardKOneClass_restrict _ _ _ _ _

/-- The affine specialization retains the native rank-one structure sheaf and forward unit. -/
theorem polynomialScalarForwardKOneClass_restrict_rankOne (R : CommRingCat.{u}) :
    perfectOpenKRestrict (laurentToPolynomial R) 1
        (perfectScalarForwardKOneClass (laurentToPolynomial R)
          (rankOnePerfectComplex (Spec (.of (Polynomial R))))
          (polynomialCoordinate R) (laurentCoordinate R)
          (laurentToPolynomial_appTop_coordinate R)) =
      perfectGlobalUnitKOneClass _ (laurentCoordinate R)
        (rankOnePerfectComplex (Spec (.of (LaurentPolynomial R)))) :=
  perfectScalarForwardKOneClass_restrict_rankOne _ _ _ _

attribute [colib_tag "COL-0305"] polynomialScalarForwardKOneClass_restrict
  polynomialScalarForwardKOneClass_restrict_rankOne

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarLaurentClassComparison.lean:85-107"
  "adaptation" "On native polynomial and Laurent spectra over every commutative ring, the
    actual coordinate X restricts to the independent fine class of the actual forward unit T 1"]
  polynomialScalarForwardKOneClass_restrict polynomialScalarForwardKOneClass_restrict_rankOne

end AlgebraicGeometry.Scheme.Modules
