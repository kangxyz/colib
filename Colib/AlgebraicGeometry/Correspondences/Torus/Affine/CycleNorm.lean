/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.DivisorEquivalence
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialSpanNorm
public import Colib.RingTheory.Polynomial.BoundaryOneRationalFunctions.PointedQuotient

/-!
# Determinant norms on actual native affine torus cycles

Each native prime contributes the determinant norm of its actual coordinate
unit in its whole finite support algebra. Signed native coefficients multiply
these norms with their literal integer exponents. Comparison with the produced
coordinate polynomial proves compatibility with the actual rational divisor.
The kernel is the sum of boundary-one divisors and the actual identity graph.

The normal integral Noetherian affine scope is retained. This module does not
identify the quotient by that graph with a presheaf cokernel, prove arbitrary
coefficient pullback compatibility, or perform descent to disconnected schemes.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial TopologicalSpace Stacks.Chow
open Polynomial.BoundaryOneRationalFunctions

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]

namespace PrimePoint

variable {f : Spec (.of R) ⟶ S} (Z : PrimePoint f)

omit [IsDomain R] [IsIntegrallyClosed R] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The chart coordinate is the pullback of the original native ambient torus unit. -/
theorem coordinateUnit_eq_native :
    Z.coordinateUnit = Units.map Z.inclusion.appTop.hom.toMonoidHom (ambientCoordinate f) := by
  apply Units.ext
  have h := congrArg
    (fun u : (Γ(ambient f, ⊤))ˣ => Z.inclusion.appTop (u : Γ(ambient f, ⊤)))
    (chartInverse_unit f)
  change Z.inclusion.appTop ((chartInverse f).appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (chartUnit (R := R) :
      LaurentPolynomial R))) = Z.inclusion.appTop (ambientCoordinate f : Γ(ambient f, ⊤)) at h
  change (Z.inclusion ≫ chartInverse f).appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (chartUnit (R := R) :
      LaurentPolynomial R)) = Z.inclusion.appTop (ambientCoordinate f : Γ(ambient f, ⊤))
  rw [Scheme.Hom.comp_appTop]
  exact h

/-- The original finite support is genuinely free by its produced whole-quotient presentation. -/
theorem coordinateFree : Module.Free R Z.coordinateRing :=
  Module.Free.of_equiv' Z.coordinatePolynomial_monic.free_adjoinRoot
    Z.polynomialEquiv.toLinearEquiv

/-- The determinant norm of the actual forward unit on the whole native prime support. -/
def coordinateNorm : Rˣ := Units.map (Algebra.norm R) Z.coordinateUnit

/-- The produced full algebra equivalence preserves this actual determinant norm. -/
theorem coordinateNorm_eq_rootNormUnit :
    Z.coordinateNorm =
      AdjoinRoot.rootNormUnit Z.coordinatePolynomial Z.coordinatePolynomial_constant_isUnit := by
  apply Units.ext
  change Algebra.norm R (Z.coordinateUnit : Z.coordinateRing) = _
  rw [← Z.polynomialEquiv_root, Algebra.norm_eq_of_algEquiv,
    AdjoinRoot.rootNormUnit_val]

/-- The actual support determinant norm is the signed value of its literal defining function. -/
theorem coordinateNorm_eq_signedValue :
    Z.coordinateNorm = signedValueHom Z.rationalFunction := by
  rw [Z.coordinateNorm_eq_rootNormUnit, rationalFunction,
    signedValueHom_polynomial_eq_rootNormUnit]
  rfl

end PrimePoint

/-- The actual finite-support signed sum of prime-support determinant norms. -/
def cycleNorm (f : Spec (.of R) ⟶ S) :
    finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) →+ Additive Rˣ :=
  liftFiniteCorrespondence f (multiplicativeGroupBaseChange S ↘ S)
    (fun z hz => Additive.ofMul (PrimePoint.coordinateNorm (⟨z, hz⟩ : PrimePoint f)))

omit [IsDomain R] [IsIntegrallyClosed R] in
/-- Signed native prime coefficients become literal integer powers of the actual norm. -/
@[simp] theorem cycleNorm_single (f : Spec (.of R) ⟶ S)
    (z : ambient f) (hz : IsFiniteCorrespondencePoint f
      (multiplicativeGroupBaseChange S ↘ S) z) (n : ℤ) :
    cycleNorm f (singleFiniteCorrespondence f
        (multiplicativeGroupBaseChange S ↘ S) z hz n) =
      n • Additive.ofMul (PrimePoint.coordinateNorm (⟨z, hz⟩ : PrimePoint f)) :=
  liftFiniteCorrespondence_single _ _ _ _ _ _

/-- The independently defined prime determinant norm agrees with the actual fraction invariant. -/
theorem cycleNorm_eq_signedValue_comp (f : Spec (.of R) ⟶ S) :
    cycleNorm f = signedValueHom.toAdditive.comp (cycleRationalFunction f) := by
  apply finiteCorrespondences.addHom_ext_one f (multiplicativeGroupBaseChange S ↘ S)
  intro z hz
  simp only [cycleNorm_single, AddMonoidHom.comp_apply, cycleRationalFunction_single,
    one_zsmul]
  exact congrArg Additive.ofMul
    (PrimePoint.coordinateNorm_eq_signedValue (⟨z, hz⟩ : PrimePoint f))

variable [IsNoetherianRing R]

/-- The genuine divisor and actual support determinant norm commute on every signed fraction. -/
@[simp] theorem cycleNorm_rationalDivisor (f : Spec (.of R) ⟶ S)
    (a : admissibleGroup R) :
    cycleNorm f (rationalDivisor f a) = Additive.ofMul (signedValueHom a) := by
  rw [cycleNorm_eq_signedValue_comp, AddMonoidHom.comp_apply]
  change signedValueHom.toAdditive (cycleRationalFunction f
    (rationalDivisorHom f (Additive.ofMul a))) = _
  rw [cycleRationalFunction_rationalDivisorHom]
  rfl

/-- Whole polynomial cycles, including repeated factors, have the genuine geometric span norm. -/
theorem cycleNorm_denominator (f : Spec (.of R) ⟶ S) (p : denominators R) :
    cycleNorm f (denominatorCycle f p) = Additive.ofMul (spanNorm f p.val p.property.2) := by
  rw [cycleNorm_eq_signedValue_comp, AddMonoidHom.comp_apply,
    cycleRationalFunction_denominator]
  exact congrArg Additive.ofMul (signedValueHom_polynomial_eq_spanNorm f p)

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] in
/-- The actual literal linear denominator uses the same sign convention. -/
theorem unitDenominator_eq_linearDenominator (v : Rˣ) :
    unitDenominator v = linearDenominator (-v) := by
  apply Subtype.ext
  simp [unitDenominator, linearDenominator, sub_eq_add_neg]

/-- The direct support norm takes the native graph of a unit to that unit. -/
@[simp] theorem cycleNorm_unitGraph (f : Spec (.of R) ⟶ S) (v : Rˣ)
    (hR : (genericPoints (Spec (.of R))).Finite) :
    cycleNorm f (unitGraphCycle f v hR) = Additive.ofMul v := by
  rw [← rationalDivisor_linear f v hR, cycleNorm_rationalDivisor,
    unitDenominator_eq_linearDenominator, signedValueHom_linear]

/-- Every base unit is attained by its actual native graph. -/
theorem cycleNorm_surjective (f : Spec (.of R) ⟶ S) : Function.Surjective (cycleNorm f) := by
  intro v
  exact ⟨unitGraphCycle f v.toMul
    (AlgebraicCycle.fundamentalCycle_genericPoints_finite (Spec (.of R))),
    cycleNorm_unitGraph f v.toMul _⟩

omit [IsIntegrallyClosed R] in
/-- The literal identity-point fraction maps to the actual native identity graph. -/
theorem rationalDivisor_identityPoint (f : Spec (.of R) ⟶ S)
    (hR : (genericPoints (Spec (.of R))).Finite) :
    rationalDivisor f (identityPointFraction (R := R)) = unitGraphCycle f 1 hR := by
  change rationalDivisor f (admissibleFraction (linearDenominator (-1 : Rˣ)) 1) = _
  rw [← unitDenominator_eq_linearDenominator]
  exact rationalDivisor_linear f 1 hR

/-- Actual boundary-one divisors lie in the actual support determinant-norm kernel. -/
@[simp] theorem cycleNorm_boundaryDivisor (f : Spec (.of R) ⟶ S)
    (m : Additive (group R)) : cycleNorm f (boundaryDivisor f m) = 0 := by
  change cycleNorm f (rationalDivisor f (boundaryInclusion m.toMul)) = _
  rw [cycleNorm_rationalDivisor, signedValueHom_boundaryInclusion]
  rfl

/-- Boundary-one divisors and integer multiples of the actual identity graph intersect trivially. -/
theorem boundaryDivisor_identityGraph_intersection (f : Spec (.of R) ⟶ S)
    (hR : (genericPoints (Spec (.of R))).Finite)
    (m : Additive (group R)) (d : ℤ)
    (h : boundaryDivisor f m = d • unitGraphCycle f 1 hR) : m = 0 ∧ d = 0 := by
  have he : Additive.ofMul (boundaryInclusion m.toMul) =
      Additive.ofMul (identityPointFraction (R := R) ^ d) := by
    apply rationalDivisorHom_injective f
    change boundaryDivisor f m = rationalDivisor f (identityPointFraction ^ d)
    rw [rationalDivisor_zpow, rationalDivisor_identityPoint f hR]
    exact h
  obtain ⟨hm, hd⟩ := boundary_identityPoint_intersection m.toMul d
    (congrArg Additive.toMul he)
  exact ⟨Additive.toMul.injective hm, hd⟩

/-- Exactness before reduction: the kernel is boundary-one divisors plus
the literal unit-one graph. -/
theorem cycleNorm_eq_zero_iff (f : Spec (.of R) ⟶ S)
    (hR : (genericPoints (Spec (.of R))).Finite)
    (c : finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S)) :
    cycleNorm f c = 0 ↔ ∃ (m : Additive (group R)) (d : ℤ),
      c = boundaryDivisor f m + d • unitGraphCycle f 1 hR := by
  constructor
  · intro hc
    have hn : signedValueHom (cycleRationalFunction f c).toMul = 1 := by
      have h := congrArg Additive.toMul hc
      rw [cycleNorm_eq_signedValue_comp, AddMonoidHom.comp_apply] at h
      change signedValueHom (cycleRationalFunction f c).toMul = 1 at h
      exact h
    obtain ⟨m, hm⟩ := signedValue_kernel_decomposition (cycleRationalFunction f c).toMul hn
    refine ⟨Additive.ofMul m, fractionDegree (cycleRationalFunction f c).toMul, ?_⟩
    have h := rationalDivisorHom_cycleRationalFunction f c
    change rationalDivisor f (cycleRationalFunction f c).toMul = c at h
    rw [hm, rationalDivisor_mul, rationalDivisor_zpow,
      rationalDivisor_identityPoint f hR] at h
    exact h.symm
  · rintro ⟨m, d, rfl⟩
    rw [map_add, map_zsmul, cycleNorm_boundaryDivisor, cycleNorm_unitGraph]
    change (0 : Additive Rˣ) + d • 0 = 0
    simp

end AlgebraicGeometry.NativeTorusPolynomial
