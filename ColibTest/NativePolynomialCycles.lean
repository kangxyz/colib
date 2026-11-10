/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.NativeStalkMultiplicity
import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.AmbientNaturality
import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialSpanNorm
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic

/-! Actual native polynomial-cycle consumers. All examples are source-only until the native gate. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial TopologicalSpace
open AlgebraicGeometry.NativeTorusPolynomial Stacks.Chow
open Polynomial.BoundaryOneRationalFunctions

universe u

variable {S T : Scheme.{u}} {R : Type u} [CommRing R]

local instance : IsSeparated (multiplicativeGroupBaseChange S ↘ S) := by
  change IsSeparated (pullback.snd
    (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ)))
    (specULiftZIsTerminal.from S))
  infer_instance

example (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    IsClosedImmersion (inclusion f p hu) := inclusion_isClosedImmersion f p hu

example (f : Spec (.of R) ⟶ S) :
    (nativeChartIso f).hom ≫ (nativeChartIso f).inv = 𝟙 _ := (nativeChartIso f).hom_inv_id

example (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    chartQuotient p hu ≫ (nativeChartIso f).hom = inclusion f p hu :=
  chartQuotient_chartMap f p hu

example (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    (inclusion f p hu).appTop.hom.comp (ambientPolynomial f) =
      (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv.hom.comp (AdjoinRoot.mk p) :=
  inclusion_appTop_ambientPolynomial f p hu

example (p : R[X]) (hp : p.Monic) (x : Spec (.of (LaurentPolynomial R))) :
    chartPolynomialGerm p x ∈
      nonZeroDivisors ((Spec (.of (LaurentPolynomial R))).presheaf.stalk x) :=
  chartPolynomialGerm_regular p hp x

example (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) (x : ambient f) :
    IdealSheafData.stalk (inclusion f p hu).ker x = Ideal.span {nativePolynomialGerm f p x} :=
  inclusion_ker_stalk f p hu x

variable [IsNoetherianRing R]

example (f : Spec (.of R) ⟶ S) (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0)) :
    finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) := polynomialCycle f p hp hu

example (f : Spec (.of R) ⟶ S) (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0))
    (x : genericPoints (Spec (.of (AdjoinRoot p)))) :
    (polynomialCycle f p hp hu).val (inclusion f p hu x.val) =
      ((Module.length ((Spec (.of (AdjoinRoot p))).presheaf.stalk x.val)
        ((Spec (.of (AdjoinRoot p))).presheaf.stalk x.val)).toNat : ℤ) :=
  polynomialCycle_apply_generic f p hp hu x

example (f : Spec (.of R) ⟶ S) (p q : R[X]) (hp : p.Monic) (hq : q.Monic)
    (hp0 : IsUnit (p.coeff 0)) (hq0 : IsUnit (q.coeff 0)) :
    polynomialCycle f (p * q) (hp.mul hq) (by simpa using hp0.mul hq0) =
      polynomialCycle f p hp hp0 + polynomialCycle f q hq hq0 :=
  polynomialCycle_mul f p q hp hq hp0 hq0

example (f : Spec (.of R) ⟶ S) (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0)) :
    polynomialCycle f (p ^ 7) (hp.pow 7)
        (by simpa only [coeff_zero_eq_eval_zero, eval_pow] using hu.pow 7) =
      7 • polynomialCycle f p hp hu := polynomialCycle_pow f p hp hu 7

example (f : Spec (.of R) ⟶ S) (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0)) :
    (-3 : ℤ) • polynomialCycle f (p ^ 7) (hp.pow 7)
        (by simpa only [coeff_zero_eq_eval_zero, eval_pow] using hu.pow 7) =
      (-3 : ℤ) • (7 • polynomialCycle f p hp hu) := by rw [polynomialCycle_pow]

example (f : Spec (.of R) ⟶ S) :
    polynomialCycle f (1 : R[X]) monic_one (by simp) = 0 := polynomialCycle_one f

-- A nonreduced linear quotient retains the fundamental multiplicities of its source.
example (f : Spec (.of R) ⟶ S) (v : Rˣ) :
    letI : IsClosedImmersion (unitGraphMap f v) :=
      isClosedImmersion_correspondenceGraphMap _ _ _ _
    (polynomialCycle f (Polynomial.X - C (v : R)) (monic_X_sub_C _)
      (linear_constant_isUnit v)).val =
        finiteCyclePushforward (unitGraphMap f v)
          (AlgebraicCycle.fundamentalCycle (Spec (.of R))) :=
  polynomialCycle_linear_fundamental f v

example (f : Spec (.of R) ⟶ S) (p q : denominators R) :
    rationalDivisor f (admissibleFraction p q) = denominatorCycle f p - denominatorCycle f q :=
  rationalDivisor_fraction f p q

example (f : Spec (.of R) ⟶ S) (a : admissibleGroup R) :
    rationalDivisor f (a ^ (-3 : ℤ)) = (-3 : ℤ) • rationalDivisor f a :=
  rationalDivisor_zpow f a (-3)

example (f : Spec (.of R) ⟶ S) (a b : admissibleGroup R) :
    rationalDivisor f (a * b) = rationalDivisor f a + rationalDivisor f b :=
  rationalDivisor_mul f a b

example (f : Spec (.of R) ⟶ S) (p q r s : denominators R) (h : fraction p q = fraction r s) :
    denominatorCycle f p - denominatorCycle f q = denominatorCycle f r - denominatorCycle f s :=
  divisor_presentation_independent f p q r s h

example (f : Spec (.of R) ⟶ S) (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0))
    (x : ambient f) (hx : pullback.fst f (multiplicativeGroupBaseChange S ↘ S) x ∈
      genericPoints (Spec (.of R))) : nativeQuotientStalkLength f p x ≠ ⊤ :=
  nativeQuotientStalkLength_ne_top f p hp hu x hx

example (f : Spec (.of R) ⟶ S) (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0))
    (x : ambient f) (hx : pullback.fst f (multiplicativeGroupBaseChange S ↘ S) x ∈
      genericPoints (Spec (.of R))) :
    (polynomialCycle f p hp hu).val x = ((nativeQuotientStalkLength f p x).toNat : ℤ) :=
  polynomialCycle_apply_native f p hp hu x hx

example (f : Spec (.of R) ⟶ S) (g : Spec (.of R) ⟶ T) (a : admissibleGroup R) :
    finiteCyclePushforward (ambientChangeIso f g).hom (rationalDivisor f a).val =
      (rationalDivisor g a).val := rationalDivisor_ambientChangeIso f g a

example [_root_.IsReduced R] (f : Spec (.of R) ⟶ S) (v : Rˣ)
    (hR : (genericPoints (Spec (.of R))).Finite) :
    polynomialCycle f (Polynomial.X - C (v : R)) (monic_X_sub_C _) (linear_constant_isUnit v) =
      unitGraphCycle f v hR := polynomialCycle_linear_graph f v hR

example [_root_.IsReduced R] (f : Spec (.of R) ⟶ S) (v w : Rˣ)
    (hR : (genericPoints (Spec (.of R))).Finite) :
    rationalDivisor f (admissibleFraction (unitDenominator v) (unitDenominator w) ^ (-3 : ℤ)) =
      (-3 : ℤ) • unitGraphCycle f v hR - (-3 : ℤ) • unitGraphCycle f w hR :=
  rationalDivisor_linear_fraction_zpow f v w hR (-3)

-- The repeated-factor product theorem also works over a genuinely nonreduced coefficient ring.
example (p q : (ZMod 4)[X]) (hp : p.Monic) (hq : q.Monic)
    (hp0 : IsUnit (p.coeff 0)) (hq0 : IsUnit (q.coeff 0)) :
    polynomialCycle (𝟙 (Spec (.of (ZMod 4)))) (p * q) (hp.mul hq)
        (by simpa using hp0.mul hq0) =
      polynomialCycle (𝟙 _) p hp hp0 + polynomialCycle (𝟙 _) q hq hq0 :=
  polynomialCycle_mul (𝟙 _) p q hp hq hp0 hq0

-- The zero coefficient ring is not removed by an implicit nontriviality premise.
example : polynomialCycle (𝟙 (Spec (.of (ZMod 1)))) (1 : (ZMod 1)[X])
    monic_one (by simp) = 0 := polynomialCycle_one _

-- No small-universe coefficient model is substituted for the actual affine ring.
example (p q : denominators (ULift.{u + 1} ℤ)) :
    letI : IsNoetherianRing (ULift.{u + 1} ℤ) :=
      isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
    rationalDivisor (𝟙 (Spec (.of (ULift.{u + 1} ℤ)))) (admissibleFraction p q) =
      denominatorCycle (𝟙 _) p - denominatorCycle (𝟙 _) q := by
  have : IsNoetherianRing (ULift.{u + 1} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  exact rationalDivisor_fraction (𝟙 _) p q

-- The same actual fractions retain the already constructed geometric coordinate norm.
example (f : Spec (.of R) ⟶ S) (p q : denominators R) :
    signedValueHom (admissibleFraction p q) =
      spanNorm f p.val p.property.2 / spanNorm f q.val q.property.2 :=
  signedValueHom_fraction_eq_spanNorm_div f p q
