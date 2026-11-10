/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialProducts
public import Colib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Admissible

/-!
# Signed divisors of actual admissible localized fractions

The source is the existing subgroup of units of the actual polynomial
localization. The target is the existing native finite-correspondence group.
Cross multiplication and the proved whole-cycle product law give presentation
independence. No formal fraction group, desired inverse, or norm assumption is
introduced. Surjectivity and inverse recovery of arbitrary native generators
remain separate geometric theorems.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial TopologicalSpace
open Polynomial.BoundaryOneRationalFunctions Stacks.Chow

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The actual native polynomial cycle of a denominator in the original localization. -/
def denominatorCycle (f : Spec (.of R) ⟶ S) (p : denominators R) :
    finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) :=
  polynomialCycle f p.val p.property.1 p.property.2

@[simp] theorem denominatorCycle_one (f : Spec (.of R) ⟶ S) :
    denominatorCycle f (1 : denominators R) = 0 := polynomialCycle_one f

theorem denominatorCycle_mul (f : Spec (.of R) ⟶ S) (p q : denominators R) :
    denominatorCycle f (p * q) = denominatorCycle f p + denominatorCycle f q :=
  polynomialCycle_mul f p.val q.val p.property.1 q.property.1 p.property.2 q.property.2

/-- Equality in the original localized ring gives equality of actual signed cycles. -/
theorem divisor_presentation_independent (f : Spec (.of R) ⟶ S)
    (p q r s : denominators R) (h : fraction p q = fraction r s) :
    denominatorCycle f p - denominatorCycle f q =
      denominatorCycle f r - denominatorCycle f s := by
  have he := (fraction_eq_iff p q r s).mp h
  have hc := congrArg (denominatorCycle f) (show p * s = r * q from Subtype.ext he)
  rw [denominatorCycle_mul, denominatorCycle_mul] at hc
  exact sub_eq_sub_iff_add_eq_add.mpr hc

/-- A single native divisor agrees with every actual fraction presentation. -/
theorem exists_rationalDivisor (f : Spec (.of R) ⟶ S) (a : admissibleGroup R) :
    ∃ z : finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S),
      ∀ p q : denominators R, a.val = fraction p q →
        z = denominatorCycle f p - denominatorCycle f q := by
  obtain ⟨p, q, ha⟩ := a.property
  exact ⟨_, fun r s h => divisor_presentation_independent f p q r s (ha.symm.trans h)⟩

/-- The actual signed rational divisor in the retained native torus correspondence group. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Torus/Affine/RationalDivisor.lean:40-111"
  "adaptation" "Actual localization fractions and proved native whole polynomial cycles"]
def rationalDivisor (f : Spec (.of R) ⟶ S) (a : admissibleGroup R) :
    finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) :=
  (exists_rationalDivisor f a).choose

theorem rationalDivisor_eq (f : Spec (.of R) ⟶ S) (a : admissibleGroup R)
    (p q : denominators R) (h : a.val = fraction p q) :
    rationalDivisor f a = denominatorCycle f p - denominatorCycle f q :=
  (exists_rationalDivisor f a).choose_spec p q h

@[simp] theorem rationalDivisor_fraction (f : Spec (.of R) ⟶ S) (p q : denominators R) :
    rationalDivisor f (admissibleFraction p q) =
      denominatorCycle f p - denominatorCycle f q := rationalDivisor_eq _ _ p q rfl

@[simp] theorem rationalDivisor_one (f : Spec (.of R) ⟶ S) :
    rationalDivisor f (1 : admissibleGroup R) = 0 := by
  rw [rationalDivisor_eq f _ 1 1 (fraction_self 1).symm, sub_self]

theorem rationalDivisor_mul (f : Spec (.of R) ⟶ S) (a b : admissibleGroup R) :
    rationalDivisor f (a * b) = rationalDivisor f a + rationalDivisor f b := by
  obtain ⟨p, q, ha⟩ := a.property
  obtain ⟨r, s, hb⟩ := b.property
  have hab : (a * b).val = fraction (p * r) (q * s) := by
    change a.val * b.val = _
    rw [ha, hb, fraction_mul]
  rw [rationalDivisor_eq f _ _ _ hab, rationalDivisor_eq f _ _ _ ha,
    rationalDivisor_eq f _ _ _ hb, denominatorCycle_mul, denominatorCycle_mul]
  abel

/-- The rational divisor is a genuine homomorphism on the actual localization subgroup. -/
def rationalDivisorHom (f : Spec (.of R) ⟶ S) : Additive (admissibleGroup R) →+
    finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) where
  toFun a := rationalDivisor f a.toMul
  map_zero' := rationalDivisor_one f
  map_add' a b := rationalDivisor_mul f a.toMul b.toMul

/-- Every integer exponent becomes its literal signed multiple of the native cycle. -/
theorem rationalDivisor_zpow (f : Spec (.of R) ⟶ S) (a : admissibleGroup R) (n : ℤ) :
    rationalDivisor f (a ^ n) = n • rationalDivisor f a :=
  (rationalDivisorHom f).map_zsmul n (Additive.ofMul a)

@[simp] theorem rationalDivisor_inv (f : Spec (.of R) ⟶ S) (a : admissibleGroup R) :
    rationalDivisor f a⁻¹ = -rationalDivisor f a :=
  (rationalDivisorHom f).map_neg (Additive.ofMul a)

/-- The original boundary-one subgroup maps into the same native integer cycles. -/
def boundaryDivisor (f : Spec (.of R) ⟶ S) : Additive (group R) →+
    finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) :=
  (rationalDivisorHom f).comp boundaryInclusion.toAdditive

/-- A linear denominator in the original actual localization. -/
def unitDenominator (v : Rˣ) : denominators R :=
  ⟨Polynomial.X - C (v : R), monic_X_sub_C _, linear_constant_isUnit v⟩

/-- The genuine divisor of the linear fraction is the existing native graph cycle. -/
theorem rationalDivisor_linear [_root_.IsReduced R] (f : Spec (.of R) ⟶ S) (v : Rˣ)
    (hR : (genericPoints (Spec (.of R))).Finite) :
    rationalDivisor f (admissibleFraction (unitDenominator v) 1) =
      unitGraphCycle f v hR := by
  rw [rationalDivisor_fraction, denominatorCycle_one, sub_zero]
  exact polynomialCycle_linear_graph f v hR

/-- Signed ratios of linear factors give differences of actual native unit graphs. -/
theorem rationalDivisor_linear_fraction_zpow [_root_.IsReduced R] (f : Spec (.of R) ⟶ S) (v w : Rˣ)
    (hR : (genericPoints (Spec (.of R))).Finite) (n : ℤ) :
    rationalDivisor f (admissibleFraction (unitDenominator v) (unitDenominator w) ^ n) =
      n • unitGraphCycle f v hR - n • unitGraphCycle f w hR := by
  rw [rationalDivisor_zpow, rationalDivisor_fraction]
  change n • (polynomialCycle f _ _ _ - polynomialCycle f _ _ _) = _
  dsimp only [unitDenominator]
  rw [polynomialCycle_linear_graph f v hR, polynomialCycle_linear_graph f w hR, smul_sub]

end AlgebraicGeometry.NativeTorusPolynomial
