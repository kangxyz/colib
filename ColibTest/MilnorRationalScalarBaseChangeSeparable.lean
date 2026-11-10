/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.RationalScalarBaseChangeSeparable

open Polynomial Stacks.Chow MonicIrreducibleOfDegree
open scoped RatFunc
attribute [local instance] Polynomial.algebra Ideal.Quotient.field

universe u

local instance milnorRationalScalarBaseChangeTestIrreducibleSeparable {F : Type u} [Field F]
    {n : ℕ} (r : MonicIrreducibleOfDegree F n) : Fact (Irreducible (poly r)) :=
  ⟨irreducible r⟩

local instance milnorRationalScalarBaseChangeTestRootFiniteSeparable {F : Type u} [Field F]
    {n : ℕ} (r : MonicIrreducibleOfDegree F n) :
    Module.Finite F (AdjoinRoot (poly r)) :=
  (AdjoinRoot.powerBasis (ne_zero r)).finite

local instance milnorRationalScalarBaseChangeTestRationalFiniteSeparable {F : Type u} [Field F]
    {n : ℕ} (r : MonicIrreducibleOfDegree F n) :
    Module.Finite (RatFunc F) (RatFunc (AdjoinRoot (poly r))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible r).natDegree_pos)

variable {k K : Type u} [Field k] [Field K] {d : ℕ}
  (φ : k →+* K) (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable) (hp : d.Prime)
  [Normal k (AdjoinRoot (poly p))]

-- Actual chosen norms, actual coefficient-root maps, and original multiplicities.
example (S : Finset (Σ e : ℕ, MonicIrreducibleOfDegree K e))
    (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly p).map φ)
    (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))) :
    milnorKRingMap
        (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ))
        (milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p))) x) =
      ∑ i ∈ S.attach, (multiplicity (poly i.1.2) ((poly p).map φ) : ℤ) •
        milnorKNormRing (RatFunc K) (RatFunc (AdjoinRoot (poly i.1.2)))
          (milnorKRingMap
            (RatFunc.mapRingHom
              (Polynomial.mapRingHom
                (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)))
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom
                (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)))) x) :=
  milnorKNormRing_ratFunc_map_eq_sum_coefficientFactors_of_normal_prime_of_separable
      φ p hsep hp S hS x

-- A single exact finite set works for every class; coverage is not an input.
example :
    ∃ (S : Finset (Σ e : ℕ, MonicIrreducibleOfDegree K e))
      (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly p).map φ),
      ∀ x : MilnorKRing (RatFunc (AdjoinRoot (poly p))),
        milnorKRingMap
            (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ))
            (milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p))) x) =
          ∑ i ∈ S.attach, (multiplicity (poly i.1.2) ((poly p).map φ) : ℤ) •
            milnorKNormRing (RatFunc K) (RatFunc (AdjoinRoot (poly i.1.2)))
              (milnorKRingMap
                (RatFunc.mapRingHom
                  (Polynomial.mapRingHom
                    (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)))
                  (Polynomial.nonZeroDivisors_le_comap_mapRingHom
                    (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)))) x) :=
  exists_finset_milnorKNormRing_ratFunc_map_eq_sum_coefficientFactors_of_normal_prime_of_separable
      φ p hsep hp

-- Degree-one factors have the same literal square and are never excluded.
example (q : MonicIrreducibleOfDegree K 1) (hq : poly q ∣ (poly p).map φ) :
    let φR : RatFunc k →+* RatFunc K :=
      RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
    let j : RatFunc (AdjoinRoot (poly p)) →+* RatFunc (AdjoinRoot (poly q)) :=
      RatFunc.mapRingHom (Polynomial.mapRingHom (AdjoinRoot.map φ (poly p) (poly q) hq))
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom
          (AdjoinRoot.map φ (poly p) (poly q) hq))
    (AdjoinRoot.rationalCoefficientAlgEquiv (poly q) (monic q)).symm.toRingHom.comp j =
      (AdjoinRoot.map φR (poly p.ratFunc) (poly q.ratFunc)
        (Polynomial.dvd_map_ratFunc_C_mapRingHom φ (poly p) (poly q) hq)).comp
          (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom :=
  AdjoinRoot.rationalCoefficientAlgEquiv_symm_mapRingHom
    φ (poly p) (poly q) (monic p) (monic q) hq

-- The coefficient weights in the final theorem really are unchanged multiplicities.
example {e : ℕ} (q : MonicIrreducibleOfDegree K e) :
    multiplicity (poly q.ratFunc)
        ((poly p.ratFunc).map
          (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
            (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ))) =
      multiplicity (poly q) ((poly p).map φ) :=
  (congrArg (multiplicity (poly q.ratFunc))
    (Polynomial.map_ratFunc_C_mapRingHom φ (poly p))).trans
      (multiplicity_ratFunc q ((poly p).map φ))
