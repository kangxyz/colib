/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.NativePrimePresentation
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.RationalDivisor
public import Colib.AlgebraicGeometry.Chow.IntegralFundamental
public import Colib.AlgebraicGeometry.Correspondences.Additive.Ext

/-!
# Actual rational functions of native signed torus cycles

Every admissible native point supplies its literal coordinate minimal
polynomial. The existing finite-support lift combines those polynomials with
the original integer coefficients in the actual localization group. The
whole-quotient isomorphism proves recovery of every native signed cycle.
No desired inverse, scalar kernel, generic equation, or norm law is assumed.

Provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Correspondences/Torus/Affine/PolynomialCycles.lean:144-161`,
`RationalDivisor.lean:115-141`, `DivisorEquivalence.lean:34-64`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin Polynomial.BoundaryOneRationalFunctions

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]

namespace PrimePoint

variable {f : Spec (.of R) ⟶ S} (Z : PrimePoint f)

/-- The genuine monic, constant-unit equation in the retained denominator monoid. -/
def denominator : denominators R :=
  ⟨Z.coordinatePolynomial, Z.coordinatePolynomial_monic, Z.coordinatePolynomial_constant_isUnit⟩

/-- The literal normalized function of an actual native prime support. -/
def rationalFunction : admissibleGroup R := admissibleFraction Z.denominator 1

variable [IsNoetherianRing R]

instance supportNoetherian : IsNoetherian Z.support where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian Z.projection
  toCompactSpace := inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole quotient cycle is exactly the native admissible prime with coefficient one. -/
theorem polynomialCycle_eq_single :
    polynomialCycle f Z.coordinatePolynomial Z.coordinatePolynomial_monic
        Z.coordinatePolynomial_constant_isUnit =
      singleFiniteCorrespondence f (multiplicativeGroupBaseChange S ↘ S) Z.val Z.property 1 := by
  classical
  have := inclusion_isClosedImmersion f Z.coordinatePolynomial
    Z.coordinatePolynomial_constant_isUnit
  apply Subtype.ext
  rw [polynomialCycle_val]
  have h := finiteCyclePushforward_comp_apply Z.polynomialSupportIso.hom Z.inclusion
    (AlgebraicCycle.fundamentalCycle (Spec (.of (AdjoinRoot Z.coordinatePolynomial))))
  rw [finiteCyclePushforward_fundamentalCycle_iso Z.polynomialSupportIso,
    finiteCyclePushforward_fundamentalCycle_integral] at h
  have he : finiteCyclePushforward
      (NativeTorusPolynomial.inclusion f Z.coordinatePolynomial
        Z.coordinatePolynomial_constant_isUnit)
      (AlgebraicCycle.fundamentalCycle (Spec (.of (AdjoinRoot Z.coordinatePolynomial)))) =
        single (Z.inclusion (genericPoint Z.support)) (1 : ℤ) := by
    simpa only [Z.polynomialSupportIso_inclusion] using h.symm
  rw [he]
  change single (genericPointOf (integralComponentAt Z.val)
    (isIntegral_integralComponentAt Z.val)) (1 : ℤ) = single Z.val 1
  rw [genericPointOf_integralComponentAt]

@[simp] theorem rationalDivisor_rationalFunction :
    rationalDivisor f Z.rationalFunction =
      singleFiniteCorrespondence f (multiplicativeGroupBaseChange S ↘ S) Z.val Z.property 1 := by
  rw [rationalFunction, rationalDivisor_fraction, denominatorCycle_one, sub_zero]
  exact Z.polynomialCycle_eq_single

end PrimePoint

/-- Multiply actual native support equations with all their signed integer multiplicities. -/
def cycleRationalFunction (f : Spec (.of R) ⟶ S) :
    finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) →+
      Additive (admissibleGroup R) :=
  liftFiniteCorrespondence f (multiplicativeGroupBaseChange S ↘ S)
    (fun z hz => Additive.ofMul (PrimePoint.rationalFunction (⟨z, hz⟩ : PrimePoint f)))

@[simp] theorem cycleRationalFunction_single (f : Spec (.of R) ⟶ S)
    (z : ambient f) (hz : IsFiniteCorrespondencePoint f
      (multiplicativeGroupBaseChange S ↘ S) z) (n : ℤ) :
    cycleRationalFunction f
        (singleFiniteCorrespondence f (multiplicativeGroupBaseChange S ↘ S) z hz n) =
      n • Additive.ofMul (PrimePoint.rationalFunction (⟨z, hz⟩ : PrimePoint f)) :=
  liftFiniteCorrespondence_single _ _ _ _ _ _

variable [IsNoetherianRing R]

/-- The actual rational divisor recovers every signed native finite correspondence. -/
@[simp] theorem rationalDivisorHom_cycleRationalFunction (f : Spec (.of R) ⟶ S)
    (c : finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S)) :
    rationalDivisorHom f (cycleRationalFunction f c) = c := by
  have h : (rationalDivisorHom f).comp (cycleRationalFunction f) = AddMonoidHom.id _ := by
    apply finiteCorrespondences.addHom_ext_one f (multiplicativeGroupBaseChange S ↘ S)
    intro z hz
    rw [AddMonoidHom.comp_apply, cycleRationalFunction_single, one_zsmul]
    exact PrimePoint.rationalDivisor_rationalFunction (⟨z, hz⟩ : PrimePoint f)
  exact DFunLike.congr_fun h c

/-- Every native signed torus cycle has a produced actual admissible fraction. -/
theorem rationalDivisorHom_surjective (f : Spec (.of R) ⟶ S) :
    Function.Surjective (rationalDivisorHom f) :=
  fun c => ⟨cycleRationalFunction f c, rationalDivisorHom_cycleRationalFunction f c⟩

/-- The recovery map itself is injective on native signed cycles. -/
theorem cycleRationalFunction_injective (f : Spec (.of R) ⟶ S) :
    Function.Injective (cycleRationalFunction f) :=
  Function.LeftInverse.injective (rationalDivisorHom_cycleRationalFunction f)

end AlgebraicGeometry.NativeTorusPolynomial
