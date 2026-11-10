/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import StacksCore.RingTheory.Polynomial.FreeQuotient

/-!
# The actual root unit and its norm in a monic polynomial quotient

An invertible constant coefficient makes the literal root in `R[X]/(p)` a
unit. For monic `p`, its norm is `(-1)^natDegree p * coeff p 0` over every
commutative ring. The proof uses Mathlib's actual finite free power basis and
the native Stacks minimal-polynomial computation, not a supplied norm law.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {R : Type*} [CommRing R]

/-- An invertible constant coefficient makes the forward polynomial coordinate a unit. -/
theorem isUnit_root_of_isUnit_coeff_zero (p : R[X]) (hp : IsUnit (p.coeff 0)) :
    IsUnit (root p) := by
  have h := congrArg (mk p) (X_mul_divX_add p)
  simp only [map_add, map_mul, mk_X, mk_C, mk_self] at h
  have hprod : root p * mk p p.divX = -of p (p.coeff 0) :=
    eq_neg_of_add_eq_zero_left h
  apply isUnit_of_mul_isUnit_left (y := mk p p.divX)
  rw [hprod]
  exact (hp.map (of p)).neg

/-- The actual forward-coordinate unit in the polynomial quotient. -/
def rootUnit (p : R[X]) (hp : IsUnit (p.coeff 0)) : (AdjoinRoot p)ˣ :=
  (isUnit_root_of_isUnit_coeff_zero p hp).unit

@[simp] theorem rootUnit_val (p : R[X]) (hp : IsUnit (p.coeff 0)) :
    (rootUnit p hp : AdjoinRoot p) = root p := IsUnit.unit_spec _

/-- Norm of the actual quotient-coordinate unit using the native determinant norm. -/
def rootNormUnit (p : R[X]) (hp : IsUnit (p.coeff 0)) : Rˣ :=
  Units.map (Algebra.norm R) (rootUnit p hp)

@[simp] theorem rootNormUnit_val (p : R[X]) (hp : IsUnit (p.coeff 0)) :
    (rootNormUnit p hp : R) = Algebra.norm R (root p) := by
  change Algebra.norm R (rootUnit p hp : AdjoinRoot p) = _
  rw [rootUnit_val]

/-- The literal root norm is the signed constant coefficient over any commutative ring. -/
theorem norm_root_of_monic (p : R[X]) (hp : p.Monic) :
    Algebra.norm R (root p) = (-1 : R) ^ p.natDegree * p.coeff 0 := by
  have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (powerBasis' hp)
  change Algebra.norm R (root p) =
    (-1 : R) ^ p.natDegree * (minpoly R (root p)).coeff 0 at h
  rwa [hp.minpoly_adjoinRoot] at h

/-- The genuine unit norm retains its concrete signed coefficient. -/
theorem rootNormUnit_val_of_monic (p : R[X]) (hp : p.Monic)
    (hu : IsUnit (p.coeff 0)) :
    (rootNormUnit p hu : R) = (-1 : R) ^ p.natDegree * p.coeff 0 := by
  rw [rootNormUnit_val, norm_root_of_monic p hp]

end AdjoinRoot
