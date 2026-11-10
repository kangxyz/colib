/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialSpanNorm
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.QuotientStalkMultiplicity

/-! # Actual consumers of native torus polynomial spans and their coordinate norms -/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace
open AlgebraicGeometry.NativeTorusPolynomial Polynomial.BoundaryOneRationalFunctions
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

variable {S : Scheme.{u}} {R : Type u} [CommRing R]

example (f : Spec (.of R) ⟶ S) (p : denominators R) :
    IsFinite (inclusion f p.val p.property.2) :=
  inclusion_isFinite f p.val p.property.1 p.property.2

example (p : denominators R) : Flat (projection p.val) :=
  projection_flat p.val p.property.1

example (f : Spec (.of R) ⟶ S) (p : denominators R) :
    (coordinateUnit f p.val p.property.2 : AdjoinRoot p.val) = AdjoinRoot.root p.val :=
  coordinateUnit_val f p.val p.property.2

example (f : Spec (.of R) ⟶ S) (v : Rˣ) :
    inclusion f (Polynomial.X - C (v : R)) (linear_constant_isUnit v) =
      projection (Polynomial.X - C (v : R)) ≫ unitGraphMap f v :=
  inclusion_linear f v

example (f : Spec (.of R) ⟶ S) :
    (nativeAffineTorusPoint f 1).left = f ≫
      (Scheme.SmoothSite.torusInsertOne S 0 0).left ≫
      (Scheme.SmoothSite.torusPowerOneIso S).hom.left :=
  affineUnitPoint_one_recursive f

example (f : Spec (.of R) ⟶ S) (v : Rˣ)
    (hR : (genericPoints (Spec (.of R))).Finite) :
    ((-3 : ℤ) • unitGraphCycle f v hR).1 =
      (-3 : ℤ) • ∑ t ∈ hR.toFinset, single (unitGraphMap f v t) 1 :=
  zsmul_unitGraphCycle_coe f v hR (-3)

example (f : Spec (.of R) ⟶ S) (p q : denominators R) :
    signedValueHom (admissibleFraction p q ^ (-3 : ℤ)) =
      (spanNorm f p.val p.property.2 / spanNorm f q.val q.property.2) ^ (-3 : ℤ) :=
  signedValueHom_fraction_zpow_eq_spanNorm_div f p q (-3)

example (f : Spec (.of R) ⟶ S) :
    spanNorm f (Polynomial.X - C (1 : R)) (linear_constant_isUnit (1 : Rˣ)) = 1 :=
  spanNorm_linear_one f

example (f : Spec (.of PUnit) ⟶ S) (p : denominators PUnit) :
    signedValueHom (admissibleFraction p 1) = spanNorm f p.val p.property.2 :=
  signedValueHom_polynomial_eq_spanNorm f p

example {T : Scheme.{0}} (f : Spec (.of ℤ[X]) ⟶ T) (p : denominators ℤ[X]) :
    spanNorm (Spec.map (CommRingCat.ofHom (evalRingHom (0 : ℤ))) ≫ f)
      (denominatorMap (evalRingHom (0 : ℤ)) p).val
      (denominatorMap (evalRingHom (0 : ℤ)) p).property.2 =
      Units.map (evalRingHom (0 : ℤ)).toMonoidHom (spanNorm f p.val p.property.2) :=
  spanNorm_denominatorMap f (evalRingHom (0 : ℤ)) p

example (f : Spec (.of R) ⟶ S) (p q : denominators R) :
    (ULift.up (signedValueHom (admissibleFraction p q)) : ULift.{u + 1} Rˣ) =
      ULift.up (spanNorm f p.val p.property.2 / spanNorm f q.val q.property.2) :=
  congrArg ULift.up (signedValueHom_fraction_eq_spanNorm_div f p q)

example (x : PrimeSpectrum R[X]) (p q : R[X]) (hq : q.Monic) :
    quotientStalkLength x (p * q) = quotientStalkLength x p + quotientStalkLength x q :=
  quotientStalkLength_mul x p q hq

example (x : PrimeSpectrum R[X]) (v : Rˣ) :
    quotientStalkLength x ((Polynomial.X - C (v : R)) ^ 2) =
      2 • quotientStalkLength x (Polynomial.X - C (v : R)) :=
  quotientStalkLength_pow x _ (monic_X_sub_C _) 2

example (x : PrimeSpectrum R[X])
    [IsNoetherianRing (polynomialStalk x)] [Ring.KrullDimLE 1 (polynomialStalk x)]
    (p q : R[X]) (hp : p.Monic) (hq : q.Monic) :
    (-3 : ℤ) • quotientStalkMultiplicity x (p * q) =
      (-3 : ℤ) • quotientStalkMultiplicity x p + (-3 : ℤ) • quotientStalkMultiplicity x q :=
  zsmul_quotientStalkMultiplicity_mul x p q hp hq (-3)
