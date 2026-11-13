/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.Basic

/-! # The full polynomial quotient is the complement of its principal open -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Spec/PolynomialQuotient/PolynomialQuotientComplement.lean`, blob
`09f1fa2ad263220dbf43d26708913b584cbfe201`.
Only the actual generic fiber receives a curve-dimension bound. The original
total space, overlap and full finite boundary are retained. Ordinary cohomology
uses the native free-Yoneda Ext source.
-/

@[expose] public noncomputable section
open AlgebraicGeometry Polynomial
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient

/-- The original whole quotient has the full complement as its underlying image.
There is no passage to the reduced quotient. -/
theorem range_inclusion_complement {R : Type u} [CommRing R] (f : R[X]) :
    Set.range (inclusion f) = (principalOpen f : Set (Spec (.of R[X])))ᶜ := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {f}))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]
  ext x
  simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
  change f ∈ x.asIdeal ↔ ¬¬ f ∈ x.asIdeal
  exact not_not.symm

end AlgebraicGeometry.PolynomialOpenQuotient
