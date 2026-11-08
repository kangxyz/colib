/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectLaurentUnitComparison
import Colib.AlgebraicGeometry.KTheory.PerfectPolynomialUnitComparison
import Colib.AlgebraicGeometry.KTheory.PerfectScalarSupportedBoundary

/-! Regressions for coarse-to-fine unit comparison, both signs, and native Laurent coordinates. -/

noncomputable section
open CategoryTheory Waldhausen Fibration AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent
universe u

section Scalar
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

-- The source is still the independently defined actual coarse weak-arrow class.
example : perfectScalarForwardKOneClass j K r q hq =
    (perfectOpenNested j).coarse.weakEndomorphismKOneClass ((perfectGlobalScalar X r).app K)
      (quasiIso_restrict_complexGlobalScalar j r q hq K.obj) := rfl

example : perfectOpenKRestrict j 1 (perfectScalarForwardKOneClass j K r q hq) =
    perfectGlobalUnitKOneClass U q ((perfectComplexesRestrictOpenImmersion j).obj K) :=
  perfectScalarForwardKOneClass_restrict j K r q hq

-- Restriction has positive forward orientation and inverse cofiber orientation.
example : perfectOpenKRestrict j 1 (perfectScalarCofiberBoundaryKOneClass j K r q hq) =
    (perfectGlobalUnitKOneClass U q ((perfectComplexesRestrictOpenImmersion j).obj K))⁻¹ :=
  perfectScalarCofiberBoundaryKOneClass_restrict j K r q hq

example (hi : j.appTop r = ↑(q⁻¹)) :
    perfectOpenKRestrict j 1 (perfectScalarForwardKOneClass j K r q⁻¹ hi) =
      (perfectGlobalUnitKOneClass U q ((perfectComplexesRestrictOpenImmersion j).obj K))⁻¹ :=
  perfectScalarForwardKOneClass_restrict_inv j K r q hi

-- The separate COL-0304 relative connecting map still gives the positive signed cone.
example : perfectOpenConnectingHom j 0 (perfectScalarForwardKOneClass j K r q hq) =
    (perfectSupportedWaldhausen j).kZeroObjectClass
      ((perfectSupportedScalarConeFunctor j r q hq).obj K) :=
  perfectOpenConnectingHom_scalarForward j K r q hq

end Scalar

section Laurent
variable (X : Scheme.{u}) (R : CommRingCat.{u})

-- The relative source is the existing native Stacks base change, for any base scheme.
example : perfectOpenKRestrict (multiplicativeGroupBaseChangeToAdditive X) 1
      (perfectScalarForwardKOneClass (multiplicativeGroupBaseChangeToAdditive X)
        (rankOnePerfectComplex (additiveGroupBaseChange X))
        (additiveGroupBaseChangeCoordinate X) (multiplicativeGroupBaseChangeCoordinate X)
        (multiplicativeGroupBaseChangeToAdditive_appTop_coordinate X)) =
    perfectGlobalUnitKOneClass (multiplicativeGroupBaseChange X)
      (multiplicativeGroupBaseChangeCoordinate X)
      (rankOnePerfectComplex (multiplicativeGroupBaseChange X)) :=
  perfectLaurentScalarForwardKOneClass_restrict_rankOne X

example : perfectOpenKRestrict (multiplicativeGroupBaseChangeToAdditive X) 1
      (perfectScalarCofiberBoundaryKOneClass (multiplicativeGroupBaseChangeToAdditive X)
        (rankOnePerfectComplex (additiveGroupBaseChange X))
        (additiveGroupBaseChangeCoordinate X) (multiplicativeGroupBaseChangeCoordinate X)
        (multiplicativeGroupBaseChangeToAdditive_appTop_coordinate X)) =
    (perfectGlobalUnitKOneClass (multiplicativeGroupBaseChange X)
      (multiplicativeGroupBaseChangeCoordinate X)
      (rankOnePerfectComplex (multiplicativeGroupBaseChange X)))⁻¹ :=
  perfectLaurentScalarCofiberBoundaryKOneClass_restrict_rankOne X

-- The affine open is literally Spec.map of the original toLaurent ring homomorphism.
example : laurentToPolynomial R =
    Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)) :=
  rfl

example : (laurentCoordinate R).val =
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv.hom (LaurentPolynomial.T 1) :=
  IsUnit.unit_spec _

example : perfectOpenKRestrict (laurentToPolynomial R) 1
      (perfectScalarForwardKOneClass (laurentToPolynomial R)
        (rankOnePerfectComplex (Spec (.of (Polynomial R))))
        (polynomialCoordinate R) (laurentCoordinate R) (laurentToPolynomial_appTop_coordinate R)) =
    perfectGlobalUnitKOneClass _ (laurentCoordinate R)
      (rankOnePerfectComplex (Spec (.of (LaurentPolynomial R)))) :=
  polynomialScalarForwardKOneClass_restrict_rankOne R

end Laurent
