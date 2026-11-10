/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.CoefficientNaturality
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.CycleNorm

/-!
# Rational functions and norms of actual coefficient fibers

These statements concern the whole native support-fiber cycles constructed in
`CoefficientNaturality`. Their rational functions are the literal coefficient
specializations, and their independently defined support determinant norms are
the coefficient images of the original determinant norms. Every signed integer
multiplicity is retained.

The maps of coefficient rings need not be flat or injective. No target transfer
on units is used. This is not yet graph-precomposition naturality: the missing
comparison between actual Tor composition and these actual fiber cycles remains
explicitly separate. No conditional graph naturality theorem is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial Stacks.Chow Polynomial.BoundaryOneRationalFunctions

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial.PrimePoint

variable {S : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]
  [IsDomain R] [IsIntegrallyClosed R]
  [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  {f : Spec (.of R) ⟶ S} (Z : PrimePoint f)

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- The whole fiber gives the mapped denominator in the original native cycle group. -/
theorem coefficientFiberCycle_eq_denominatorCycle (a : R →+* A) :
    Z.coefficientFiberCycle a =
      denominatorCycle (Spec.map (CommRingCat.ofHom a) ≫ f) (denominatorMap a Z.denominator) :=
  Z.coefficientFiberCycle_eq_polynomialCycle a

/-- Actual rational recovery on the whole scheme-theoretic fiber keeps its literal equation. -/
theorem cycleRationalFunction_coefficientFiberCycle (a : R →+* A) :
    cycleRationalFunction (Spec.map (CommRingCat.ofHom a) ≫ f) (Z.coefficientFiberCycle a) =
      Additive.ofMul (admissibleMap a Z.rationalFunction) := by
  rw [Z.coefficientFiberCycle_eq_denominatorCycle, cycleRationalFunction_denominator]
  simp only [rationalFunction, admissibleMap_fraction, map_one]

/-- The norm of the actual whole support fiber is the coefficient image of its support norm. -/
theorem cycleNorm_coefficientFiberCycle (a : R →+* A) :
    cycleNorm (Spec.map (CommRingCat.ofHom a) ≫ f) (Z.coefficientFiberCycle a) =
      Additive.ofMul (Units.map a.toMonoidHom Z.coordinateNorm) := by
  rw [cycleNorm_eq_signedValue_comp, AddMonoidHom.comp_apply,
    Z.cycleRationalFunction_coefficientFiberCycle]
  change Additive.ofMul (signedValueHom (admissibleMap a Z.rationalFunction)) = _
  rw [signedValueHom_natural, Z.coordinateNorm_eq_signedValue]

/-- Signed native multiplicities remain literal signed powers after support base change. -/
theorem cycleNorm_zsmul_coefficientFiberCycle (a : R →+* A) (n : ℤ) :
    cycleNorm (Spec.map (CommRingCat.ofHom a) ≫ f) (n • Z.coefficientFiberCycle a) =
      Additive.ofMul ((Units.map a.toMonoidHom Z.coordinateNorm) ^ n) := by
  rw [map_zsmul, Z.cycleNorm_coefficientFiberCycle]
  rfl

/-- Recovery retains every signed multiplicity of the unreduced coefficient fiber. -/
theorem cycleRationalFunction_zsmul_coefficientFiberCycle (a : R →+* A) (n : ℤ) :
    cycleRationalFunction (Spec.map (CommRingCat.ofHom a) ≫ f)
        (n • Z.coefficientFiberCycle a) =
      Additive.ofMul (admissibleMap a (Z.rationalFunction ^ n)) := by
  rw [map_zsmul, Z.cycleRationalFunction_coefficientFiberCycle, map_zpow]
  rfl

/-- The same norm formula written directly against the original native signed prime. -/
theorem cycleNorm_coefficientFiberCycle_eq_map_single (a : R →+* A) (n : ℤ) :
    cycleNorm (Spec.map (CommRingCat.ofHom a) ≫ f) (n • Z.coefficientFiberCycle a) =
      (Units.map a.toMonoidHom).toAdditive
        (cycleNorm f (singleFiniteCorrespondence f
          (multiplicativeGroupBaseChange S ↘ S) Z.val Z.property n)) := by
  rw [map_zsmul, Z.cycleNorm_coefficientFiberCycle, cycleNorm_single, map_zsmul]
  rfl

end AlgebraicGeometry.NativeTorusPolynomial.PrimePoint
