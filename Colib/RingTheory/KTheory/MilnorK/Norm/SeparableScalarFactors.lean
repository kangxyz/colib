/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ScalarFactorBaseChange
public import Mathlib.FieldTheory.Separable

/-!
# Simple-norm base change over all literal separable scalar factors

The native coefficient-factor subtype is finite. If the original polynomial is
separable, every factor has multiplicity one in its coefficient image. The
unconditional scalar-factor formula therefore becomes an unweighted sum over
the entire literal subtype. No alternative factor model or norm is introduced.

-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace Stacks.Chow.MonicIrreducibleOfDegree

/-- A finite enumeration of the literal complete coefficient-factor subtype. -/
@[instance_reducible]
def coefficientFactorFintype {k : Type u} [Field k] {K : Type v} [Field K]
    (φ : k →+* K) (p : k[X]) (hp : p ≠ 0) :
    Fintype {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ p.map φ} := by
  classical
  let S := (exists_finset_mem_iff_dvd_map φ p hp).choose
  exact Fintype.subtype S (exists_finset_mem_iff_dvd_map φ p hp).choose_spec

/-- Each actual irreducible factor of a separable coefficient image has multiplicity one. -/
theorem multiplicity_eq_one_of_separable_map
    {k : Type u} [Field k] {K : Type v} [Field K]
    (φ : k →+* K) {d e : ℕ} (p : MonicIrreducibleOfDegree k d)
    (q : MonicIrreducibleOfDegree K e) (hp : (poly p).Separable)
    (hq : poly q ∣ (poly p).map φ) :
    multiplicity (poly q) ((poly p).map φ) = 1 := by
  have hfinite : FiniteMultiplicity (poly q) ((poly p).map φ) :=
    FiniteMultiplicity.of_not_isUnit (irreducible q).not_isUnit
      (Polynomial.map_ne_zero (ne_zero p))
  apply hfinite.multiplicity_eq_iff.mpr
  constructor
  · simpa only [pow_one] using hq
  · intro hsq
    apply (irreducible q).not_isUnit
    apply Polynomial.isUnit_of_self_mul_dvd_separable (hp.map (f := φ))
    change poly q ^ 2 ∣ (poly p).map φ at hsq
    simpa only [pow_two] using hsq

end Stacks.Chow.MonicIrreducibleOfDegree

namespace Stacks.Chow

open MonicIrreducibleOfDegree

local instance separableScalar_nativeIrreducible {F : Type*} [Field F]
    {d : ℕ} (r : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly r)) :=
  ⟨irreducible r⟩
attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

/-- Base change over every actual scalar factor, with multiplicity one proved from
separability. The finite enumeration is arbitrary, but its carrier is the full subtype. -/
theorem simpleMilnorNorm_map_eq_sum_scalarFactors_of_separable
    (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (hp : (poly p).Separable)
    [Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
      poly r.2 ∣ (poly p).map φ}]
    (x : MilnorKRing (AdjoinRoot (poly p))) :
    milnorKRingMap φ (simpleMilnorNorm p x) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
          poly r.2 ∣ (poly p).map φ},
        simpleMilnorNorm r.1.2
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly r.1.2) r.2) x) := by
  classical
  let I := {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
    poly r.2 ∣ (poly p).map φ}
  have hinj : Set.InjOn (fun r : I => poly r.1.2) (↑(Finset.univ : Finset I) : Set I) := by
    intro r _ s _ hrs
    exact Subtype.ext (sigma_poly_injective hrs)
  have hcover : ∀ (e : ℕ) (q : MonicIrreducibleOfDegree K e),
      poly q ∣ (poly p).map φ →
        ∃ r ∈ (Finset.univ : Finset I), poly q = poly r.1.2 := by
    intro e q hq
    exact ⟨⟨⟨e, q⟩, hq⟩, Finset.mem_univ _, rfl⟩
  have hsum := simpleMilnorNorm_map_eq_weighted_sum_of_factors
    φ p x (Finset.univ : Finset I) (fun r => r.1.1) (fun r => r.1.2)
    hinj (fun r => r.2) hcover
  have hm (r : I) : multiplicity (poly r.1.2) ((poly p).map φ) = 1 :=
    multiplicity_eq_one_of_separable_map φ p r.1.2 hp r.2
  apply hsum.trans
  apply Finset.sum_congr rfl
  intro r _
  rw [hm r, Nat.cast_one, one_zsmul]
  rfl

/-- Characteristic zero supplies separability of the original native irreducible polynomial. -/
theorem simpleMilnorNorm_map_eq_sum_scalarFactors [CharZero k]
    (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    [Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
      poly r.2 ∣ (poly p).map φ}]
    (x : MilnorKRing (AdjoinRoot (poly p))) :
    milnorKRingMap φ (simpleMilnorNorm p x) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
          poly r.2 ∣ (poly p).map φ},
        simpleMilnorNorm r.1.2
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly r.1.2) r.2) x) :=
  simpleMilnorNorm_map_eq_sum_scalarFactors_of_separable φ p (irreducible p).separable x

end Stacks.Chow

end
