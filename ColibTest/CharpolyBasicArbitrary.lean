/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Charpoly.BasicArbitrary

/-! Actual finite-field and unrestricted consumers of the multiplication power formula. -/

@[expose] public noncomputable section

namespace ColibTest.CharpolyBasicArbitrary

/-- The full formula is available over an arbitrary original field. -/
theorem actual_charpoly_power {k L : Type*} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] (a : L) :
    (Algebra.lmul k L a).charpoly =
      (minpoly k a) ^ Module.finrank (IntermediateField.adjoin k {a}) L :=
  Algebra.charpoly_lmul_eq_minpoly_pow_arbitrary a

/-- A finite base field is admitted without supplying an incompatible Infinite instance. -/
theorem actual_finite_field_charpoly_power {k L : Type*} [Field k] [Finite k]
    [Field L] [Algebra k L] [FiniteDimensional k L] (a : L) :
    (Algebra.lmul k L a).charpoly =
      (minpoly k a) ^ Module.finrank (IntermediateField.adjoin k {a}) L :=
  Algebra.charpoly_lmul_eq_minpoly_pow_arbitrary a

end ColibTest.CharpolyBasicArbitrary
