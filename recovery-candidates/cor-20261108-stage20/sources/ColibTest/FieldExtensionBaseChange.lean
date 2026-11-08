/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.RingTheory.Length.FieldExtensionBaseChange

noncomputable section

open scoped TensorProduct

universe u v

-- Even an identity field extension retains the local base's full nonreduced multiplicity.
example (K : Type u) (R : Type v) [Field K] [CommRing R] [IsLocalRing R]
    [Algebra K R] [IsArtinianRing R] :
    ∑ᶠ q : MaximalSpectrum (R ⊗[K] K),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) *
        (Module.finiteAlgebraResidueDegree R (R ⊗[K] K) q : ℤ) =
      ((Module.length R R).toNat : ℤ) := by
  simpa only [Module.finrank_self, Nat.cast_one, one_mul] using
    Module.finsum_natCast_length_mul_residueDegree_tensor_fieldExtension K K R

#check Module.length_tensor_fieldExtension
#check Module.finsum_length_mul_residueDegree_tensor_fieldExtension
#check Module.finsum_natCast_length_mul_residueDegree_tensor_fieldExtension
