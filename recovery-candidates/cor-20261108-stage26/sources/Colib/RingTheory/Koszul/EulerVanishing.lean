/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Koszul.GenericEuler

/-!
# Integer Koszul Euler of a zero coefficient module

Vanishing of the coefficient module implies degreewise vanishing of the native
Koszul homology and hence zero integer Euler. No finiteness, regularity, local
ring, or ideal-of-definition hypothesis is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ExteriorAlgebra TensorProduct

universe u v

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}
  (f : Fin r → R) (M : Type v) [AddCommGroup M] [Module R M] [Subsingleton M]

/-- Zero coefficients give zero native Koszul homology in each degree. -/
theorem isZero_homology_seqComplexTensor_of_subsingleton (n : ℕ) :
    IsZero ((seqComplexTensor f M).homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  apply HomologicalComplex.ExactAt.of_isZero
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton ((⋀[R]^n (Fin r → R)) ⊗[R] M)
  infer_instance

/-- Integer Euler vanishes when the actual coefficient module vanishes. -/
theorem seqEuler_eq_zero_of_subsingleton : seqEuler f M = 0 := by
  have hlen (n : ℕ) : Module.length R ((seqComplexTensor f M).homology n) = 0 :=
    Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp
      (isZero_homology_seqComplexTensor_of_subsingleton f M n))
  simp [seqEuler, hlen]

end Koszul
