/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.GroupScheme.LaurentOpen
public import Mathlib.RingTheory.Polynomial.Ideal

/-!
# The closed complement of the native integral Laurent open

Adapted from the zero-section range calculation in
`Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/AffineLine/Complement.lean`
at motivic commit a6805c4a87cdfd7717dd7a94039246a167f15380,
blob 04e207934b1c046be1d982a37259855b97381acf.
Only the existing native integral additive and multiplicative schemes occur.
The closed map is literal evaluation at zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The full closed complement of the positive Laurent open is evaluation at zero. -/
theorem range_integral_zero_eq_compl_multiplicativeGroupToAdditive :
    Set.range (Spec.map (CommRingCat.ofHom
      (Polynomial.evalRingHom (0 : ULift.{u} ℤ)))) =
      (Set.range multiplicativeGroupToAdditive.{u})ᶜ := by
  change Set.range (PrimeSpectrum.comap
    (Polynomial.evalRingHom (0 : ULift.{u} ℤ))) =
      (Set.range (PrimeSpectrum.comap
        (algebraMap (Polynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ)))))ᶜ
  rw [_root_.range_comap_of_surjective _ _
    (fun x => ⟨Polynomial.C x, by simp⟩), Polynomial.ker_evalRingHom]
  rw [PrimeSpectrum.localization_away_comap_range
    (LaurentPolynomial (ULift.{u} ℤ)) Polynomial.X]
  simp only [Polynomial.C_0, sub_zero, PrimeSpectrum.zeroLocus_span]
  ext x
  simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, Set.mem_compl_iff]
  change (Polynomial.X : Polynomial (ULift.{u} ℤ)) ∈ x.asIdeal ↔
    ¬ (Polynomial.X : Polynomial (ULift.{u} ℤ)) ∉ x.asIdeal
  exact not_not.symm

end AlgebraicGeometry
