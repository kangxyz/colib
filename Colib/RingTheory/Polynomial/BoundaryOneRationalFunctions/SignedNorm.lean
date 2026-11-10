/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Invariants
public import Colib.RingTheory.AdjoinRoot.UnitNorm

/-!
# Signed values are actual polynomial quotient norms

For a monic polynomial with invertible constant coefficient, the signed value
of its actual localized fraction is the norm of the literal forward-coordinate
unit in `AdjoinRoot`. Numerator-denominator fractions give the quotient of
these actual unit norms, including their signed multiplicities.

These statements hold over arbitrary commutative rings. No domain,
irreducibility, separability, or smoothness hypothesis is imposed. The final
field-valued corollary expresses the same formula using division in the field.
This file does not yet identify polynomial quotient cycles with arbitrary
finite correspondences into the native Stacks torus.
-/

@[expose] public noncomputable section

namespace Polynomial.BoundaryOneRationalFunctions

variable {R : Type*} [CommRing R]

/-- The signed value of a polynomial is its signed constant coefficient, as a unit. -/
theorem signedValueHom_polynomial (p : denominators R) :
    signedValueHom (admissibleFraction p 1) =
      (-1 : Rˣ) ^ (p : R[X]).natDegree * denominatorConstant p := by
  have h1 : denominatorConstant (1 : denominators R) = 1 := by
    apply Units.ext
    simp
  change (-1 : Rˣ) ^ fractionDegree (admissibleFraction p 1) *
    zeroValueHom (admissibleFraction p 1) = _
  rw [fractionDegree_fraction, zeroValueHom_fraction, h1, div_one]
  simp

/-- The literal linear equation `X - u` has signed value the specified unit `u`. -/
theorem signedValueHom_linear [Nontrivial R] (u : Rˣ) :
    signedValueHom (admissibleFraction (linearDenominator (-u)) 1) = u := by
  rw [signedValueHom_polynomial, linearDenominator_natDegree, pow_one,
    denominatorConstant_linear]
  apply Units.ext
  simp

/-- The actual signed value equals the native norm of the literal quotient-coordinate unit. -/
theorem signedValueHom_polynomial_eq_rootNormUnit (p : denominators R) :
    signedValueHom (admissibleFraction p 1) =
      AdjoinRoot.rootNormUnit (p : R[X]) p.property.2 := by
  apply Units.ext
  rw [signedValueHom_polynomial, AdjoinRoot.rootNormUnit_val_of_monic _ p.property.1]
  simp

/-- The actual signed-unit producer agrees with the native finite-algebra determinant norm. -/
theorem signedValueHom_polynomial_eq_norm (p : denominators R) :
    (signedValueHom (admissibleFraction p 1) : R) =
      Algebra.norm R (AdjoinRoot.root (p : R[X])) := by
  rw [signedValueHom_polynomial_eq_rootNormUnit, AdjoinRoot.rootNormUnit_val]

/-- Actual rational fractions give the quotient of actual finite-algebra unit norms. -/
theorem signedValueHom_fraction_eq_rootNormUnit_div (p q : denominators R) :
    signedValueHom (admissibleFraction p q) =
      AdjoinRoot.rootNormUnit (p : R[X]) p.property.2 /
        AdjoinRoot.rootNormUnit (q : R[X]) q.property.2 := by
  have he : admissibleFraction p q = admissibleFraction p 1 / admissibleFraction q 1 := by
    apply Subtype.ext
    change fraction p q = fraction p 1 / fraction q 1
    simp [fraction]
  rw [he, _root_.map_div, signedValueHom_polynomial_eq_rootNormUnit,
    signedValueHom_polynomial_eq_rootNormUnit]

variable {S : Type*} [CommRing S]

/-- The actual polynomial-quotient unit norm commutes with every coefficient specialization. -/
theorem rootNormUnit_denominatorMap (φ : R →+* S) (p : denominators R) :
    AdjoinRoot.rootNormUnit (denominatorMap φ p : S[X]) (denominatorMap φ p).property.2 =
      Units.map φ.toMonoidHom (AdjoinRoot.rootNormUnit (p : R[X]) p.property.2) := by
  nontriviality S
  rw [← signedValueHom_polynomial_eq_rootNormUnit,
    ← signedValueHom_polynomial_eq_rootNormUnit]
  have h := signedValueHom_natural φ (admissibleFraction p 1)
  simpa only [admissibleMap_fraction, map_one] using h

/-- The actual finite-algebra norm recovers the unit in the equation `X - u`. -/
theorem norm_root_linear [Nontrivial R] (u : Rˣ) :
    Algebra.norm R (AdjoinRoot.root (X - C (u : R))) = (u : R) := by
  rw [AdjoinRoot.norm_root_of_monic _ (monic_X_sub_C _)]
  simp

variable {K : Type*} [Field K]

/-- Over a field the unit formula is literally division of the actual determinant norms. -/
theorem signedValueHom_fraction_eq_norm_div_norm (p q : denominators K) :
    (signedValueHom (admissibleFraction p q) : K) =
      Algebra.norm K (AdjoinRoot.root (p : K[X])) /
        Algebra.norm K (AdjoinRoot.root (q : K[X])) := by
  rw [signedValueHom_fraction_eq_rootNormUnit_div, Units.val_div_eq_div_val,
    AdjoinRoot.rootNormUnit_val, AdjoinRoot.rootNormUnit_val]

end Polynomial.BoundaryOneRationalFunctions
