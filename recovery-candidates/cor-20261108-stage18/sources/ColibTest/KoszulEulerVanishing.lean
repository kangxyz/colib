/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.RingTheory.Koszul.EulerVanishing

universe u v

example {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (M : Type v) [AddCommGroup M] [Module R M] [Subsingleton M] :
    Koszul.seqEuler f M = 0 :=
  Koszul.seqEuler_eq_zero_of_subsingleton f M

#check Koszul.isZero_homology_seqComplexTensor_of_subsingleton
#check Koszul.seqEuler_eq_zero_of_subsingleton
