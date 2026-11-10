/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.LinearAlgebra.Charpoly.FiniteLength

/-! Actual native finite-length characteristic-polynomial consumers. -/

noncomputable section

universe u v w

namespace ColibTest.FiniteLengthCharpoly

/-- The original finite-dimensional operator and its native finite-length
characteristic polynomial. -/
theorem actual_field_characteristic_polynomial
    {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [Module.Finite k M]
    (hM : IsFiniteLength k M) (f : Module.End k M) :
    FiniteLengthEndomorphism.charpoly k hM f = f.charpoly.map (IsLocalRing.residue k) :=
  FiniteLengthEndomorphism.charpoly_eq_map_charpoly hM f

/-- The actual local scalar operator with its full module length and actual residue field. -/
theorem actual_scalar_characteristic_polynomial
    (R : Type u) [CommRing R] [IsLocalRing R]
    (R' : Type v) [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')]
    [Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')]
    (M' : Type w) [AddCommGroup M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']
    (hM' : IsFiniteLength R' M') (u : R') :
    let hM : IsFiniteLength R M' := Module.length_ne_top_iff.mp <| by
      rw [IsLocalRing.length_restrictScalars R R' M']
      exact WithTop.mul_ne_top (Module.length_ne_top_iff.mpr hM') (by
        rw [Module.length_eq_finrank]
        exact ENat.natCast_ne_top _)
    FiniteLengthEndomorphism.charpoly R hM
        ((LinearMap.lsmul R' M' u).restrictScalars R) =
      (Algebra.lmul (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')
        (IsLocalRing.residue R' u)).charpoly ^
        (Module.length R' M').toNat :=
  FiniteLengthEndomorphism.multiplication_charpoly_eq_pow_length R R' M' hM' u

end ColibTest.FiniteLengthCharpoly
