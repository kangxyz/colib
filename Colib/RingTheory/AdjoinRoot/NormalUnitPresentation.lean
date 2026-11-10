/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.AdjoinRoot.UnitNorm
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Actual polynomial presentation of a finite normal-base Laurent-generated domain

The algebra map is required to be torsion-free, as supplied geometrically by
dominance. Finite domain algebras with a nonzero scalar kernel do not have this
presentation. Both the unit and its inverse are integral by module finiteness.
Reversing the inverse's minimal polynomial proves the unit constant coefficient.
Normality gives the actual evaluation kernel, and the given surjective Laurent
evaluation makes the native quotient lift surjective. No kernel or inverse is
assumed. The construction works in independent universes and does not need a
Noetherian hypothesis. Source-only; no kernel acceptance is asserted.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace AdjoinRoot.NormalUnitPresentation

variable (R : Type u) {A : Type v} [CommRing R] [IsDomain R]
  [IsIntegrallyClosed R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A] [Module.Finite R A]

omit [IsDomain R] [IsIntegrallyClosed R] [IsDomain A] [Module.IsTorsionFree R A] in
/-- Module finiteness proves integrality of the actual distinguished unit. -/
theorem integral (u : Aˣ) : IsIntegral R (u : A) := IsIntegral.of_finite R _

omit [IsDomain R] [IsIntegrallyClosed R] [IsDomain A] [Module.IsTorsionFree R A] in
/-- The native minimal polynomial is monic. -/
theorem minpoly_monic (u : Aˣ) : (minpoly R (u : A)).Monic :=
  minpoly.monic (integral R u)

omit [IsDomain R] [IsIntegrallyClosed R] [IsDomain A]
  [Module.IsTorsionFree R A] [Module.Finite R A] in
/-- Reversing the inverse unit's minimal polynomial gives a relation with constant term one. -/
theorem inverse_minpoly_reverse_aeval (u : Aˣ) :
    Polynomial.aeval (u : A) (minpoly R ((u⁻¹ : Aˣ) : A)).reverse = 0 := by
  have h := (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap R A)
    ((u⁻¹ : Aˣ) : A) (minpoly R ((u⁻¹ : Aˣ) : A))).mpr
      (minpoly.aeval R ((u⁻¹ : Aˣ) : A))
  simpa only [invOf_units, inv_inv, Polynomial.aeval_def] using h

/-- The genuine constant coefficient is a unit, proved by a literal divisibility of one. -/
theorem minpoly_coeff_zero_isUnit (u : Aˣ) :
    IsUnit ((minpoly R (u : A)).coeff 0) := by
  obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd (integral R u)
    (inverse_minpoly_reverse_aeval R u)
  apply isUnit_of_dvd_one
  refine ⟨q.coeff 0, ?_⟩
  simpa only [Polynomial.coeff_zero_reverse,
    (minpoly_monic R u⁻¹).leadingCoeff, Polynomial.mul_coeff_zero] using
    congrArg (fun p : R[X] => p.coeff 0) hq

/-- Normality identifies the actual polynomial evaluation kernel. -/
theorem ker_aeval (u : Aˣ) :
    RingHom.ker (Polynomial.aeval (u : A) : R[X] →ₐ[R] A).toRingHom =
      Ideal.span {minpoly R (u : A)} :=
  minpoly.ker_eval (integral R u)

/-- The genuine minimal polynomial is prime, not only irreducible over the fraction field. -/
theorem minpoly_prime (u : Aˣ) : Prime (minpoly R (u : A)) := by
  apply (Ideal.span_singleton_prime (minpoly_monic R u).ne_zero).mp
  rw [← ker_aeval R u]
  exact RingHom.ker_isPrime _

/-- The native quotient map sending the literal root to the distinguished unit. -/
def lift (u : Aˣ) : AdjoinRoot (minpoly R (u : A)) →ₐ[R] A :=
  AdjoinRoot.liftAlgHom (minpoly R (u : A)) (Algebra.ofId R A) (u : A)
    (minpoly.aeval R (u : A))

omit [IsDomain R] [IsIntegrallyClosed R] [IsDomain A]
  [Module.IsTorsionFree R A] [Module.Finite R A] in
@[simp] theorem lift_root (u : Aˣ) :
    lift R u (AdjoinRoot.root (minpoly R (u : A))) = (u : A) := by
  exact AdjoinRoot.liftAlgHom_root (minpoly R (u : A)) (Algebra.ofId R A)
    (u : A) (minpoly.aeval R (u : A))

omit [IsDomain R] [IsIntegrallyClosed R] [IsDomain A]
  [Module.IsTorsionFree R A] [Module.Finite R A] in
@[simp] theorem lift_of (u : Aˣ) (r : R) :
    lift R u (AdjoinRoot.of (minpoly R (u : A)) r) = algebraMap R A r := by
  exact AdjoinRoot.liftAlgHom_of (minpoly R (u : A)) (Algebra.ofId R A)
    (u : A) (minpoly.aeval R (u : A)) r

/-- The actual quotient lift is injective by native minimal-polynomial divisibility. -/
theorem lift_injective (u : Aˣ) : Function.Injective (lift R u) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective (g := minpoly R (u : A)) a
  apply AdjoinRoot.mk_eq_zero.mpr
  apply minpoly.isIntegrallyClosed_dvd (integral R u)
  change Polynomial.eval₂ (algebraMap R A) (u : A) p = 0 at ha
  exact ha

theorem lift_rootUnit (u : Aˣ) :
    Units.map (lift R u).toRingHom.toMonoidHom
        (AdjoinRoot.rootUnit (minpoly R (u : A)) (minpoly_coeff_zero_isUnit R u)) = u := by
  apply Units.ext
  simp

/-- Laurent evaluation factors through the actual native polynomial quotient. -/
theorem lift_comp_laurentEval (u : Aˣ) :
    (lift R u).toRingHom.comp
        (LaurentPolynomial.eval₂ (AdjoinRoot.of (minpoly R (u : A)))
          (AdjoinRoot.rootUnit (minpoly R (u : A)) (minpoly_coeff_zero_isUnit R u))) =
      LaurentPolynomial.eval₂ (algebraMap R A) u := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : R[X]))
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_C, LaurentPolynomial.eval₂_C, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, lift_of]
  · simp only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_X, LaurentPolynomial.eval₂_T, zpow_one,
      AdjoinRoot.rootUnit_val, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, lift_root]

/-- Actual Laurent generation supplies surjectivity, rather than a chosen inverse. -/
theorem lift_surjective (u : Aˣ)
    (hgen : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R A) u)) :
    Function.Surjective (lift R u) := by
  have h : Function.Surjective ((lift R u).toRingHom.comp
      (LaurentPolynomial.eval₂ (AdjoinRoot.of (minpoly R (u : A)))
        (AdjoinRoot.rootUnit (minpoly R (u : A)) (minpoly_coeff_zero_isUnit R u)))) := by
    rw [lift_comp_laurentEval]
    exact hgen
  intro a
  obtain ⟨q, hq⟩ := h a
  exact ⟨LaurentPolynomial.eval₂ (AdjoinRoot.of (minpoly R (u : A)))
    (AdjoinRoot.rootUnit (minpoly R (u : A)) (minpoly_coeff_zero_isUnit R u)) q, hq⟩

theorem lift_bijective (u : Aˣ)
    (hgen : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R A) u)) :
    Function.Bijective (lift R u) := ⟨lift_injective R u, lift_surjective R u hgen⟩

/-- The produced native algebra equivalence, with the original base and coordinate retained. -/
def equiv (u : Aˣ)
    (hgen : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R A) u)) :
    AdjoinRoot (minpoly R (u : A)) ≃ₐ[R] A :=
  AlgEquiv.ofBijective (lift R u) (lift_bijective R u hgen)

@[simp] theorem equiv_root (u : Aˣ)
    (hgen : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R A) u)) :
    equiv R u hgen (AdjoinRoot.root (minpoly R (u : A))) = (u : A) :=
  lift_root R u

@[simp] theorem equiv_of (u : Aˣ)
    (hgen : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R A) u)) (r : R) :
    equiv R u hgen (AdjoinRoot.of (minpoly R (u : A)) r) = algebraMap R A r :=
  lift_of R u r

theorem equiv_rootUnit (u : Aˣ)
    (hgen : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R A) u)) :
    Units.map (equiv R u hgen).toRingEquiv.toRingHom.toMonoidHom
        (AdjoinRoot.rootUnit (minpoly R (u : A)) (minpoly_coeff_zero_isUnit R u)) = u :=
  lift_rootUnit R u

end AdjoinRoot.NormalUnitPresentation
