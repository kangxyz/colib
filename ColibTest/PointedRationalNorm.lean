/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Polynomial.BoundaryOneRationalFunctions.PointedQuotient
import Colib.RingTheory.Polynomial.BoundaryOneRationalFunctions.SignedNorm
import Mathlib.Algebra.Category.Grp.Ulift

/-! # Consumers of the actual pointed rational-function norm -/

noncomputable section

open CategoryTheory Polynomial
open Polynomial.BoundaryOneRationalFunctions

universe u

namespace PointedRationalNormTest

variable {R : Type u} [CommRing R]

-- No domain, smoothness, or irreducibility premise is needed for the actual root unit.
example (p : R[X]) (hp : IsUnit (p.coeff 0)) :
    (AdjoinRoot.rootUnit p hp : AdjoinRoot p) = AdjoinRoot.root p :=
  AdjoinRoot.rootUnit_val p hp

-- The producer uses the native determinant norm, not an unspecified norm function.
example (p q : denominators R) :
    signedValueHom (admissibleFraction p q) =
      Units.map (Algebra.norm R) (AdjoinRoot.rootUnit (p : R[X]) p.property.2) /
        Units.map (Algebra.norm R) (AdjoinRoot.rootUnit (q : R[X]) q.property.2) :=
  signedValueHom_fraction_eq_rootNormUnit_div p q

-- The polynomial norm formula does not silently exclude the zero ring.
example (p : denominators PUnit) :
    (signedValueHom (admissibleFraction p 1) : PUnit) =
      Algebra.norm PUnit (AdjoinRoot.root (p : PUnit[X])) :=
  signedValueHom_polynomial_eq_norm p

-- The actual finite-algebra unit norm specializes along a noninjective map.
example (p : denominators ℤ[X]) :
    AdjoinRoot.rootNormUnit (denominatorMap (evalRingHom (0 : ℤ)) p : ℤ[X])
        (denominatorMap (evalRingHom (0 : ℤ)) p).property.2 =
      Units.map (evalRingHom (0 : ℤ)).toMonoidHom
        (AdjoinRoot.rootNormUnit (p : (ℤ[X])[X]) p.property.2) :=
  rootNormUnit_denominatorMap (evalRingHom (0 : ℤ)) p

variable [Nontrivial R]

example (u : Rˣ) :
    signedValueHom (admissibleFraction (linearDenominator (-u)) 1) = u :=
  signedValueHom_linear u

-- The quotient map receives the actual polynomial equation, not an abstract preimage.
example (u : Rˣ) :
    pointedSignedValue (toPointed (admissibleFraction (linearDenominator (-u)) 1)) = u :=
  signedValueHom_linear u

-- All signed multiplicities are retained, including negative integers.
example (d : ℤ) :
    signedValueHom ((identityPointFraction (R := R)) ^ d) = 1 := by
  rw [map_zpow, signedValueHom_identityPoint, one_zpow]

example : Function.Injective (pointedBoundary (R := R)) := pointedBoundary_injective

example : Function.Surjective (pointedSignedValue (R := R)) := pointedSignedValue_surjective

example (x : pointedGroup R) :
    pointedSignedValue x = 1 ↔ ∃ m : group R, pointedBoundary m = x :=
  pointedSignedValue_eq_one_iff x

-- This is the noninjective coefficient map that occurs in simplex specialization.
example (x : pointedGroup ℤ[X]) :
    pointedSignedValue (pointedMap (evalRingHom (0 : ℤ)) x) =
      Units.map (evalRingHom (0 : ℤ)).toMonoidHom (pointedSignedValue x) :=
  pointedSignedValue_natural (evalRingHom (0 : ℤ)) x

-- Use the native large-universe functor required by the retained transfer coefficients.
def largePointedSignedValue (R : Type u) [CommRing R] [Nontrivial R] :
    (AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (AddCommGrpCat.of (Additive (pointedGroup R))) ⟶
      (AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (AddCommGrpCat.of (Additive Rˣ)) :=
  (AddCommGrpCat.uliftFunctor.{u + 1, u}).map
    (AddCommGrpCat.ofHom (pointedSignedValue (R := R)).toAdditive)

example (m : group R) :
    largePointedSignedValue R (ULift.up (Additive.ofMul (pointedBoundary m))) = 0 := by
  change ULift.up (Additive.ofMul (pointedSignedValue (pointedBoundary m))) = 0
  rw [pointedSignedValue_pointedBoundary]
  rfl

example : largePointedSignedValue R
    (ULift.up (Additive.ofMul (toPointed ((identityPointFraction (R := R)) ^ (-3 : ℤ))))) =
      0 := by
  change ULift.up (Additive.ofMul (signedValueHom (identityPointFraction ^ (-3 : ℤ)))) = 0
  rw [map_zpow, signedValueHom_identityPoint, one_zpow]
  rfl

example : Function.Surjective (largePointedSignedValue R) := by
  rintro ⟨u⟩
  change Additive Rˣ at u
  obtain ⟨x, hx⟩ := pointedSignedValue_surjective u.toMul
  refine ⟨ULift.up (Additive.ofMul x), ?_⟩
  change ULift.up (Additive.ofMul (pointedSignedValue x)) = ULift.up u
  rw [hx]
  rfl

-- The field specialization remains literally the quotient of determinant norms.
example {K : Type u} [Field K] (p q : denominators K) :
    (signedValueHom (admissibleFraction p q) : K) =
      Algebra.norm K (AdjoinRoot.root (p : K[X])) /
        Algebra.norm K (AdjoinRoot.root (q : K[X])) :=
  signedValueHom_fraction_eq_norm_div_norm p q

end PointedRationalNormTest
