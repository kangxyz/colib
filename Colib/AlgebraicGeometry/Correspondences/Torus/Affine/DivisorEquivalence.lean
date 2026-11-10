/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.PrimePolynomial
public import Colib.RingTheory.Polynomial.Normal.MonicFactorization

/-!
# Actual rational functions and native torus cycles are inverse

Normality descends every monic prime factor from the fraction field. Each factor
is identified with its actual native prime support; product additivity retains
all repetitions. The finite signed native cycle lift and the actual admissible
localization divisor are consequently inverse on the original integral normal
Noetherian affine range. Neither inverse identity is an input.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Correspondences/Torus/Affine/DivisorEquivalence.lean:66-156`. The original
regular smooth integral affine case is covered by the exact normal-domain
hypotheses, without restricting the coefficient ring to a field.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial Stacks.Chow
open Polynomial.BoundaryOneRationalFunctions

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R : Type u} [CommRing R] [IsDomain R]
  [IsIntegrallyClosed R] [IsNoetherianRing R]

@[simp] theorem rationalFunction_primePoint (f : Spec (.of R) ⟶ S)
    (p : denominators R) (hp : Prime p.val) :
    (primePoint f p.val p.property.1 p.property.2 hp).rationalFunction =
      admissibleFraction p 1 := by
  apply Subtype.ext
  change fraction _ 1 = fraction p 1
  congr 1
  apply Subtype.ext
  exact coordinatePolynomial_primePoint f p.val p.property.1 p.property.2 hp

/-- The recovery map is a genuine inverse on each actual monic prime quotient. -/
theorem cycleRationalFunction_denominator_prime (f : Spec (.of R) ⟶ S)
    (p : denominators R) (hp : Prime p.val) :
    cycleRationalFunction f (denominatorCycle f p) =
      Additive.ofMul (admissibleFraction p 1) := by
  change cycleRationalFunction f (polynomialCycle f p.val p.property.1 p.property.2) = _
  rw [polynomialCycle_eq_primePoint f _ _ _ hp, cycleRationalFunction_single,
    one_zsmul, rationalFunction_primePoint]

/-- The whole product, with every repeated factor, recovers its literal equation. -/
theorem cycleRationalFunction_denominator_prod (f : Spec (.of R) ⟶ S)
    (factors : List (denominators R)) (hf : ∀ p ∈ factors, Prime p.val) :
    cycleRationalFunction f (denominatorCycle f factors.prod) =
      Additive.ofMul (admissibleFraction factors.prod 1) := by
  induction factors with
  | nil =>
    simp only [List.prod_nil, denominatorCycle_one, map_zero, admissibleFraction_self]
    rfl
  | cons p factors ih =>
    have hp := hf p (by simp)
    have htail : ∀ q ∈ factors, Prime q.val := fun q hq => hf q (by simp [hq])
    rw [List.prod_cons, denominatorCycle_mul, map_add,
      cycleRationalFunction_denominator_prime f p hp, ih htail]
    change Additive.ofMul (admissibleFraction p 1 * admissibleFraction factors.prod 1) = _
    rw [admissibleFraction_mul, one_mul]

omit [IsNoetherianRing R] in
/-- Normality supplies the complete prime factor presentation in the actual denominator monoid. -/
theorem exists_prime_denominator_factors (p : denominators R) :
    ∃ factors : List (denominators R), factors.prod = p ∧ ∀ q ∈ factors, Prime q.val := by
  obtain ⟨factors, hf, hprime⟩ :=
    Polynomial.NormalMonicFactorization.exists_list_monic_prime_factors_of_normal
      p.val p.property.1 p.property.2
  let factors' : List (denominators R) := factors.attach.map fun q =>
    ⟨q.val, (hprime q.val q.property).1, (hprime q.val q.property).2.2⟩
  refine ⟨factors', ?_, ?_⟩
  · apply Subtype.ext
    change (denominators R).subtype factors'.prod = p.val
    rw [map_list_prod]
    simpa [factors', List.map_map] using hf
  · intro q hq
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
    exact (hprime r.val r.property).2.1

/-- Every native whole polynomial cycle recovers its literal monic equation. -/
@[simp] theorem cycleRationalFunction_denominator (f : Spec (.of R) ⟶ S)
    (p : denominators R) :
    cycleRationalFunction f (denominatorCycle f p) =
      Additive.ofMul (admissibleFraction p 1) := by
  obtain ⟨factors, rfl, hf⟩ := exists_prime_denominator_factors p
  exact cycleRationalFunction_denominator_prod f factors hf

/-- The actual normalized localized fraction is recovered from its native signed divisor. -/
@[simp] theorem cycleRationalFunction_rationalDivisorHom (f : Spec (.of R) ⟶ S)
    (a : Additive (admissibleGroup R)) :
    cycleRationalFunction f (rationalDivisorHom f a) = a := by
  obtain ⟨p, q, ha⟩ := a.toMul.property
  change cycleRationalFunction f (rationalDivisor f a.toMul) = a
  rw [rationalDivisor_eq _ _ _ _ ha, map_sub, cycleRationalFunction_denominator,
    cycleRationalFunction_denominator]
  apply congrArg Additive.ofMul
  apply Subtype.ext
  change fraction p 1 / fraction q 1 = a.toMul.val
  rw [ha]
  simp only [fraction, polynomialUnit_one, div_one]

/-- Actual admissible localization functions and actual native integer correspondences. -/
def rationalDivisorEquiv (f : Spec (.of R) ⟶ S) :
    Additive (admissibleGroup R) ≃+
      finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) where
  toFun := rationalDivisorHom f
  invFun := cycleRationalFunction f
  left_inv := cycleRationalFunction_rationalDivisorHom f
  right_inv := rationalDivisorHom_cycleRationalFunction f
  map_add' := map_add (rationalDivisorHom f)

/-- The native divisor is injective on actual normalized admissible fractions. -/
theorem rationalDivisorHom_injective (f : Spec (.of R) ⟶ S) :
    Function.Injective (rationalDivisorHom f) := (rationalDivisorEquiv f).injective

/-- The actual boundary-one divisor is injective in the native finite-correspondence group. -/
theorem boundaryDivisor_injective (f : Spec (.of R) ⟶ S) :
    Function.Injective (boundaryDivisor f) := by
  intro a b h
  apply Additive.toMul.injective
  apply Subtype.ext
  have he := (rationalDivisorEquiv f).injective h
  exact congrArg (fun x : Additive (admissibleGroup R) => x.toMul.val) he

end AlgebraicGeometry.NativeTorusPolynomial
