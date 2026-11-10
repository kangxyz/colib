/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Evaluating an irreducible polynomial localization in a local ring

If the reduction of a polynomial evaluation kills an irreducible polynomial,
its kernel is exactly that polynomial's principal ideal. Thus evaluation extends
to the original localization and is a local homomorphism. This generalizes the
origin construction to arbitrary closed points, including inseparable points.
No finiteness, separability, or coefficient-field section is assumed.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Polynomial

variable {k B : Type*} [Field k] [CommRing B] [IsLocalRing B]
  (q : k[X]) [Fact (Irreducible q)]

local instance irreducibleLocalMap_isPrime :
    (Ideal.span ({q} : Set k[X])).IsPrime :=
  (Ideal.span_singleton_prime (Fact.out : Irreducible q).ne_zero).mpr
    (Fact.out : Irreducible q).prime

/-- Reduction of evaluation has precisely the original irreducible kernel. -/
theorem residue_eval₂_eq_zero_iff_dvd (c : k →+* B) (t : B)
    (hq : residue B (q.eval₂ c t) = 0) (a : k[X]) :
    residue B (a.eval₂ c t) = 0 ↔ q ∣ a := by
  let g : AdjoinRoot q →+* ResidueField B :=
    AdjoinRoot.lift ((residue B).comp c) (residue B t)
      (by simpa only [Polynomial.hom_eval₂] using hq)
  have he (b : k[X]) : g (AdjoinRoot.mk q b) = residue B (b.eval₂ c t) := by
    rw [AdjoinRoot.lift_mk, Polynomial.hom_eval₂]
  rw [← he, ← map_zero g, g.injective.eq_iff, AdjoinRoot.mk_eq_zero]

/-- Evaluation sends exactly the complement of the irreducible ideal to units. -/
theorem isUnit_eval₂_iff_not_mem_span_irreducible (c : k →+* B) (t : B)
    (hq : residue B (q.eval₂ c t) = 0) (a : k[X]) :
    IsUnit (a.eval₂ c t) ↔ a ∉ Ideal.span ({q} : Set k[X]) := by
  rw [← residue_ne_zero_iff_isUnit, Ideal.mem_span_singleton,
    ne_eq, residue_eval₂_eq_zero_iff_dvd q c t hq]

/-- Native localization of polynomial evaluation at an arbitrary irreducible point. -/
def localizeAtIrreducibleEval₂ (c : k →+* B) (t : B)
    (hq : residue B (q.eval₂ c t) = 0) :
    Localization.AtPrime (Ideal.span ({q} : Set k[X])) →+* B :=
  IsLocalization.lift (g := Polynomial.eval₂RingHom c t)
    (fun a : (Ideal.span ({q} : Set k[X])).primeCompl =>
      (isUnit_eval₂_iff_not_mem_span_irreducible q c t hq a).mpr a.2)

/-- Localized evaluation preserves every original polynomial, not only its root. -/
theorem localizeAtIrreducibleEval₂_algebraMap (c : k →+* B) (t : B)
    (hq : residue B (q.eval₂ c t) = 0) (a : k[X]) :
    localizeAtIrreducibleEval₂ q c t hq
        (algebraMap k[X] (Localization.AtPrime (Ideal.span ({q} : Set k[X]))) a) =
      a.eval₂ c t :=
  IsLocalization.lift_eq _ a

/-- The actual extension to the original localization is a local homomorphism. -/
theorem isLocalHom_localizeAtIrreducibleEval₂ (c : k →+* B) (t : B)
    (hq : residue B (q.eval₂ c t) = 0) :
    IsLocalHom (localizeAtIrreducibleEval₂ q c t hq) := by
  apply ((IsLocalRing.local_hom_TFAE (localizeAtIrreducibleEval₂ q c t hq)).out 1 3).mpr
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_span,
    Set.image_singleton]
  apply Ideal.span_le.mpr
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  change localizeAtIrreducibleEval₂ q c t hq
    (algebraMap k[X] (Localization.AtPrime (Ideal.span ({q} : Set k[X]))) q) ∈
      maximalIdeal B
  rw [localizeAtIrreducibleEval₂_algebraMap]
  exact (residue_eq_zero_iff _).mp hq

end Polynomial
