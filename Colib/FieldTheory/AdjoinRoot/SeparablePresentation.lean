/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.AdjoinRoot.Separable

/-!
# Reading separability from an actual root-field presentation

The original root has the original monic polynomial as its minimal polynomial.
Separability of the actual field, or its embedding into a separable field, therefore
supplies separability of that polynomial. No new field model or norm is introduced.
-/

@[expose] public section

open Polynomial

namespace AdjoinRoot

/-- A monic irreducible presentation of a separable actual root field is separable. -/
theorem polynomial_separable_of_isSeparable {K : Type*} [Field K]
    (p : K[X]) [Fact (Irreducible p)] (hp : p.Monic)
    [Algebra.IsSeparable K (AdjoinRoot p)] : p.Separable := by
  have h := Algebra.IsSeparable.isSeparable K (AdjoinRoot.root p)
  change (minpoly K (AdjoinRoot.root p)).Separable at h
  simpa only [AdjoinRoot.minpoly_root hp.ne_zero, hp.leadingCoeff, inv_one,
    map_one, mul_one] using h

/-- An actual embedding into a separable field makes the monic root polynomial separable. -/
theorem polynomial_separable_of_algHom {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Algebra.IsSeparable K L]
    (p : K[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (f : AdjoinRoot p →ₐ[K] L) : p.Separable := by
  let : Algebra.IsSeparable K (AdjoinRoot p) := Algebra.IsSeparable.of_algHom K L f
  exact polynomial_separable_of_isSeparable p hp

end AdjoinRoot
