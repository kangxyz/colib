/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.LinearGraph
public import Colib.RingTheory.Polynomial.BoundaryOneRationalFunctions.SignedNorm

/-!
# Determinant norm of the actual native torus coordinate on polynomial spans

The input to the native finite-algebra norm is obtained by pulling back the
actual forward coordinate of the existing torus along the constructed scheme
map, then applying `ΓSpecIso`. It is not a norm parameter with specified laws.
The original signed rational-function invariant equals the quotient of these
geometric coordinate norms, for all monic admissible numerators and denominators.

This produces the norm on polynomial spans, including specialization and unit
graphs. It is not yet a map on all native finite correspondences: establishing
the native polynomial cycle product law and divisor inverse is still required.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial Polynomial.BoundaryOneRationalFunctions

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]

/-- The determinant norm of the pulled-back native forward torus coordinate. -/
def spanNorm (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) : Rˣ :=
  Units.map (Algebra.norm R) (coordinateUnit f p hu)

/-- The geometric coordinate norm is the actual native quotient-root norm. -/
@[simp] theorem spanNorm_eq_rootNormUnit
    (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    spanNorm f p hu = AdjoinRoot.rootNormUnit p hu := by
  rw [spanNorm, coordinateUnit_eq_rootUnit]
  rfl

/-- Its value is the actual determinant norm of the original forward quotient root. -/
theorem spanNorm_val (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    (spanNorm f p hu : R) = Algebra.norm R (AdjoinRoot.root p) := by
  rw [spanNorm_eq_rootNormUnit, AdjoinRoot.rootNormUnit_val]

/-- The monic formula holds without separability, reducedness, or field assumptions. -/
theorem spanNorm_val_of_monic (f : Spec (.of R) ⟶ S) (p : R[X])
    (hp : p.Monic) (hu : IsUnit (p.coeff 0)) :
    (spanNorm f p hu : R) = (-1 : R) ^ p.natDegree * p.coeff 0 := by
  rw [spanNorm_val, AdjoinRoot.norm_root_of_monic p hp]

/-- The actual geometric norm of the literal linear span is its specified unit. -/
theorem spanNorm_linear (f : Spec (.of R) ⟶ S) (v : Rˣ) :
    spanNorm f (Polynomial.X - C (v : R)) (linear_constant_isUnit v) = v := by
  nontriviality R
  apply Units.ext
  rw [spanNorm_val_of_monic _ _ (monic_X_sub_C _)]
  simp

/-- The original identity section has geometric coordinate norm one. -/
theorem spanNorm_linear_one (f : Spec (.of R) ⟶ S) :
    spanNorm f (Polynomial.X - C (1 : R)) (linear_constant_isUnit (1 : Rˣ)) = 1 :=
  spanNorm_linear f 1

/-- The signed value of a literal polynomial is its actual native torus-span norm. -/
theorem signedValueHom_polynomial_eq_spanNorm
    (f : Spec (.of R) ⟶ S) (p : denominators R) :
    signedValueHom (admissibleFraction p 1) = spanNorm f p.val p.property.2 := by
  rw [spanNorm_eq_rootNormUnit]
  exact signedValueHom_polynomial_eq_rootNormUnit p

/-- Actual localized fractions give quotients of the actual geometric coordinate norms. -/
theorem signedValueHom_fraction_eq_spanNorm_div
    (f : Spec (.of R) ⟶ S) (p q : denominators R) :
    signedValueHom (admissibleFraction p q) =
      spanNorm f p.val p.property.2 / spanNorm f q.val q.property.2 := by
  simp only [spanNorm_eq_rootNormUnit]
  exact signedValueHom_fraction_eq_rootNormUnit_div p q

/-- Arbitrary signed multiplicity is retained in the actual rational-function invariant. -/
theorem signedValueHom_fraction_zpow_eq_spanNorm_div
    (f : Spec (.of R) ⟶ S) (p q : denominators R) (n : ℤ) :
    signedValueHom (admissibleFraction p q ^ n) =
      (spanNorm f p.val p.property.2 / spanNorm f q.val q.property.2) ^ n := by
  rw [map_zpow, signedValueHom_fraction_eq_spanNorm_div f]

/-- Actual geometric polynomial-span norms commute with every coefficient specialization. -/
theorem spanNorm_denominatorMap (f : Spec (.of R) ⟶ S)
    (a : R →+* A) (p : denominators R) :
    spanNorm (Spec.map (CommRingCat.ofHom a) ≫ f)
      (denominatorMap a p).val (denominatorMap a p).property.2 =
      Units.map a.toMonoidHom (spanNorm f p.val p.property.2) := by
  simp only [spanNorm_eq_rootNormUnit]
  exact rootNormUnit_denominatorMap a p

end AlgebraicGeometry.NativeTorusPolynomial
