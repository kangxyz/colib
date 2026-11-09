/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Evaluating the actual origin localization in a local coefficient algebra

Given a coefficient-field map into a local ring and an element of its maximal
ideal, polynomial evaluation extends to the original localization at (X).
The denominator condition, locality, exact coordinate image and coefficient
residue formula are proved. The construction is the native IsLocalization.lift
on the actual localization, not a new local-ring or completion model.

This supplies the actual upper local map for the rational constant norm-residue
square: coefficients use the original constant-root map and the coordinate is
the image of PowerSeries.X. No finite, normal, characteristic or DVR hypothesis
is required for this local algebra construction.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Polynomial

variable {k B : Type*} [Field k] [CommRing B] [IsLocalRing B]

local instance : (Ideal.span ({X} : Set k[X])).IsPrime :=
  (Ideal.span_singleton_prime (X_ne_zero : (X : k[X]) ≠ 0)).mpr prime_X

/-- Evaluation at a target maximal-ideal element sends exactly the polynomials
outside the original origin ideal to units. -/
theorem isUnit_eval₂_iff_not_mem_span_X (c : k →+* B) {t : B}
    (ht : t ∈ maximalIdeal B) (q : k[X]) :
    IsUnit (q.eval₂ c t) ↔ q ∉ Ideal.span ({X} : Set k[X]) := by
  rw [← residue_ne_zero_iff_isUnit, Polynomial.hom_eval₂,
    (residue_eq_zero_iff t).mpr ht, Polynomial.eval₂_at_zero,
    Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
  constructor
  · intro h hz
    exact h (by rw [hz, map_zero])
  · intro h hz
    exact h (((residue B).comp c).injective (hz.trans (map_zero _).symm))

/-- The original origin localization maps to the actual target local ring by
native localization of polynomial evaluation. -/
def localizeAtOriginEval₂ (c : k →+* B) {t : B} (ht : t ∈ maximalIdeal B) :
    Localization.AtPrime (Ideal.span ({X} : Set k[X])) →+* B :=
  IsLocalization.lift (g := Polynomial.eval₂RingHom c t)
    (fun q : (Ideal.span ({X} : Set k[X])).primeCompl =>
      (isUnit_eval₂_iff_not_mem_span_X c ht q).mpr q.2)

/-- The extension preserves evaluation of every original polynomial. -/
theorem localizeAtOriginEval₂_algebraMap (c : k →+* B) {t : B}
    (ht : t ∈ maximalIdeal B) (q : k[X]) :
    localizeAtOriginEval₂ c ht
        (algebraMap k[X] (Localization.AtPrime (Ideal.span ({X} : Set k[X]))) q) =
      q.eval₂ c t := by
  exact IsLocalization.lift_eq _ q

/-- The actual origin coordinate maps to the specified maximal-ideal element. -/
theorem localizeAtOriginEval₂_X (c : k →+* B) {t : B} (ht : t ∈ maximalIdeal B) :
    localizeAtOriginEval₂ c ht
        (algebraMap k[X] (Localization.AtPrime (Ideal.span ({X} : Set k[X]))) X) = t := by
  rw [localizeAtOriginEval₂_algebraMap, Polynomial.eval₂_X]

/-- The original localization extension is a local ring homomorphism. -/
theorem isLocalHom_localizeAtOriginEval₂ (c : k →+* B) {t : B}
    (ht : t ∈ maximalIdeal B) : IsLocalHom (localizeAtOriginEval₂ c ht) := by
  apply ((IsLocalRing.local_hom_TFAE (localizeAtOriginEval₂ c ht)).out 1 3).mpr
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_span,
    Set.image_singleton]
  apply Ideal.span_le.mpr
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  change localizeAtOriginEval₂ c ht
    (algebraMap k[X] (Localization.AtPrime (Ideal.span ({X} : Set k[X]))) X) ∈
      maximalIdeal B
  rw [localizeAtOriginEval₂_X]
  exact ht

/-- Reducing the localized evaluation of an original polynomial gives its
constant coefficient through the original residue/coefficient map. -/
theorem residue_localizeAtOriginEval₂_algebraMap (c : k →+* B) {t : B}
    (ht : t ∈ maximalIdeal B) (q : k[X]) :
    residue B (localizeAtOriginEval₂ c ht
        (algebraMap k[X] (Localization.AtPrime (Ideal.span ({X} : Set k[X]))) q)) =
      residue B (c (q.coeff 0)) := by
  rw [localizeAtOriginEval₂_algebraMap, Polynomial.hom_eval₂,
    (residue_eq_zero_iff t).mpr ht, Polynomial.eval₂_at_zero, RingHom.comp_apply]

end Polynomial
