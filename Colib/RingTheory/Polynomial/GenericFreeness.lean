/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Freeness on the whole polynomial line after coefficient localization

Torsion-freeness over the fraction field's polynomial ring supplies a
finite free basis over that PID. Descend the basis through the submonoid
of nonzero coefficients and compare to the canonical tensor algebra.
The chosen denominator lies in the coefficient ring.

Adapted from Motivic at a6805c4a87cdfd7717dd7a94039246a167f15380,
`Aglib/AlgebraicGeometry/Morphisms/Finite/Flat/PolynomialGeneric.lean`
and `Aglib/RingTheory/Localization/FreeTensor.lean`.
-/

@[expose] public noncomputable section

open scoped Polynomial TensorProduct nonZeroDivisors

attribute [local instance] Polynomial.algebra

namespace Module

private theorem free_tensorProduct_of_free_localizedModule
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : Submonoid R) [IsLocalization S A]
    [Module.Free (Localization S) (LocalizedModule S B)] :
    Module.Free A (A ⊗[R] B) := by
  let e := IsLocalization.algEquiv S (Localization S) A
  let : Algebra (Localization S) (A ⊗[R] B) :=
    ((algebraMap A (A ⊗[R] B)).comp e.toRingHom).toAlgebra
  let : IsScalarTower R (Localization S) (A ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := Localization S) (A := A ⊗[R] B) fun r ↦ by
      change algebraMap R (A ⊗[R] B) r =
        algebraMap A (A ⊗[R] B) (e (algebraMap R (Localization S) r))
      rw [e.commutes, IsScalarTower.algebraMap_apply R A (A ⊗[R] B)]
  let f := IsLocalizedModule.iso S (TensorProduct.mk R A B 1)
  let f' := f.extendScalarsOfIsLocalization S (Localization S)
  let : Module.Free (Localization S) (A ⊗[R] B) := Module.Free.of_equiv f'
  let b := Module.Free.chooseBasis (Localization S) (A ⊗[R] B)
  apply Module.Free.of_basis (b.mapCoeffs e.toRingEquiv _)
  intro c x
  simp only [Algebra.smul_def]
  rfl

universe u

/-- The actual tensor algebra becomes free over the whole polynomial ring
after a nonzero principal localization of the coefficient domain. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Morphisms/Finite/Flat/PolynomialGeneric.lean:97-113"
  "adaptation" "The literal coefficient-localized polynomial tensor algebra"]
theorem exists_free_polynomial_tensorProduct_away
    (R K B : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Algebra R[X] B]
    [Module.FinitePresentation R[X] B]
    [Module.IsTorsionFree K[X] (K[X] ⊗[R[X]] B)] :
    ∃ r : R, r ≠ 0 ∧
      Module.Free (Localization.Away r)[X] ((Localization.Away r)[X] ⊗[R[X]] B) := by
  let S : Submonoid R[X] := R⁰.map Polynomial.C
  let : IsLocalization S K[X] := Polynomial.isLocalization R⁰ K
  obtain ⟨_, ⟨r, hr, rfl⟩, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers S
      (TensorProduct.mk R[X] K[X] B 1) K[X]
  let : Module.Free (Localization.Away (Polynomial.C r))
      (LocalizedModule.Away (Polynomial.C r) B) := hfree
  let : IsLocalization.Away (Polynomial.C r) (Localization.Away r)[X] := by
    simpa only [Submonoid.map_powers] using
      (Polynomial.isLocalization (Submonoid.powers r) (Localization.Away r))
  exact ⟨r, nonZeroDivisors.ne_zero hr, free_tensorProduct_of_free_localizedModule
    (Submonoid.powers (Polynomial.C r))⟩

end Module
