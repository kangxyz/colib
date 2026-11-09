/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.AdjoinRoot.RationalCoefficientMap
public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeScalarBaseChange
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalFactorIndex

/-!
# The actual rational chosen norm under coefficient extension

For a normal prime-degree root field in characteristic zero, coefficient extension
of its native chosen norm is the complete finite sum of the native chosen norms
of the rational function fields of its original coefficient factors. Every map
is the existing `RatFunc.mapRingHom` of the original `AdjoinRoot.map`.

The lower rational coefficient square is proved on the actual root-field
comparisons. Completeness of the rational factors follows from the full native
constant-factor theorem, rather than an assumed factor enumeration. The degree-one
branches are retained, and every coefficient is the original polynomial
multiplicity. Finiteness, normality, and the degree alternatives required by the
native chosen-norm comparison are obtained from their native theorems.

No norm, branch carrier, rational-function model, or tower law is introduced.
This is the rational coefficient base-change ingredient of the finite-place
argument, not the finite-place residue formula or the prime diamond.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

local instance rationalScalarBaseChangeRootIrreducible {F : Type u} [Field F]
    {n : ℕ} (r : MonicIrreducibleOfDegree F n) : Fact (Irreducible (poly r)) :=
  ⟨irreducible r⟩

local instance rationalScalarBaseChangeRootFinite {F : Type u} [Field F]
    {n : ℕ} (r : MonicIrreducibleOfDegree F n) :
    Module.Finite F (AdjoinRoot (poly r)) :=
  (AdjoinRoot.powerBasis (ne_zero r)).finite

local instance rationalScalarBaseChangeRationalFinite {F : Type u} [Field F]
    {n : ℕ} (r : MonicIrreducibleOfDegree F n) :
    Module.Finite (RatFunc F) (RatFunc (AdjoinRoot (poly r))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible r).natDegree_pos)

variable {k K : Type u} [Field k] [Field K] [CharZero k] {d : ℕ}

/-- The literal rational coefficient formula for the original chosen norm.
The finite set contains exactly the original native factors, each with its full
multiplicity. Rational factor completeness and all map compatibilities are proved. -/
theorem milnorKNormRing_ratFunc_map_eq_sum_coefficientFactors_of_normal_prime
    (φ : k →+* K) (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (AdjoinRoot (poly p))]
    (S : Finset (Σ e : ℕ, MonicIrreducibleOfDegree K e))
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
                (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)))) x) := by
  let rationalScalarBaseChangeSourceNormal :
      Normal (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
    AdjoinRoot.normal_ratFunc_adjoinRoot (poly p) (monic p)
  let φR : RatFunc k →+* RatFunc K :=
    RatFunc.mapRingHom (Polynomial.mapRingHom φ)
      (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
  let f :=
    (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm
  let q (i : S) : MonicIrreducibleOfDegree (RatFunc K) i.1.1 := i.1.2.ratFunc
  let M (i : S) := RatFunc (AdjoinRoot (poly i.1.2))
  let g (i : S) :=
    (AdjoinRoot.rationalCoefficientAlgEquiv (poly i.1.2) (monic i.1.2)).symm
  let j (i : S) : RatFunc (AdjoinRoot (poly p)) →+* M i :=
    RatFunc.mapRingHom
      (Polynomial.mapRingHom
        (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)))
      (Polynomial.nonZeroDivisors_le_comap_mapRingHom
        (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)))
  have hpoly : (poly p.ratFunc).map φR =
      ((poly p).map φ).map (RatFunc.C : K →+* RatFunc K) :=
    Polynomial.map_ratFunc_C_mapRingHom φ (poly p)
  have hq (i : S) : poly (q i) ∣ (poly p.ratFunc).map φR :=
    Polynomial.dvd_map_ratFunc_C_mapRingHom
      φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)
  have hinj : Set.InjOn (fun i : S => poly (q i)) (S.attach : Set S) := by
    intro i _ j _ hij
    apply Subtype.ext
    apply sigma_poly_injective
    exact Polynomial.map_injective (RatFunc.C : K →+* RatFunc K)
      (RatFunc.C : K →+* RatFunc K).injective hij
  have hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree (RatFunc K) a),
      poly r ∣ (poly p.ratFunc).map φR →
        ∃ i ∈ S.attach, poly r = poly (q i) := by
    intro a r hr
    have hr' : poly r ∣ ((poly p).map φ).map (RatFunc.C : K →+* RatFunc K) :=
      hpoly ▸ hr
    obtain ⟨s, hs, heq⟩ := exists_ratFunc_of_dvd_map
      ((poly p).map φ) ((monic p).map φ) ⟨a, r⟩ hr'
    let i : S := ⟨s, (hS s).mpr hs⟩
    refine ⟨i, Finset.mem_attach S i, ?_⟩
    exact (congrArg
      (fun t : Σ a : ℕ, MonicIrreducibleOfDegree (RatFunc K) a => poly t.2) heq).symm
  have hsquare (i : S) : (g i).toRingHom.comp (j i) =
      (AdjoinRoot.map φR (poly p.ratFunc) (poly (q i)) (hq i)).comp f.toRingHom :=
    AdjoinRoot.rationalCoefficientAlgEquiv_symm_mapRingHom
      φ (poly p) (poly i.1.2) (monic p) (monic i.1.2) ((hS i.1).mp i.2)
  have hmult (i : S) :
      multiplicity (poly (q i)) ((poly p.ratFunc).map φR) =
        multiplicity (poly i.1.2) ((poly p).map φ) :=
    (congrArg (multiplicity (poly (q i))) hpoly).trans
      (multiplicity_ratFunc i.1.2 ((poly p).map φ))
  have hsum := milnorKNormRing_map_eq_weighted_sum_of_branch_equivs_of_normal_prime
    φR p.ratFunc hp f S.attach (fun i => i.1.1) q hinj hq hcover M g j hsquare x
  calc
    milnorKRingMap φR
        (milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p))) x) =
        ∑ i ∈ S.attach, (multiplicity (poly (q i)) ((poly p.ratFunc).map φR) : ℤ) •
          milnorKNormRing (RatFunc K) (M i) (milnorKRingMap (j i) x) := hsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun n : ℕ => (n : ℤ) •
        milnorKNormRing (RatFunc K) (M i) (milnorKRingMap (j i) x)) (hmult i)

/-- An exact finite factor set for the actual rational chosen-norm formula exists.
No enumeration, coverage, commuting-square, or branch-norm identity is assumed. -/
theorem exists_finset_milnorKNormRing_ratFunc_map_eq_sum_coefficientFactors_of_normal_prime
    (φ : k →+* K) (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (AdjoinRoot (poly p))] :
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
                    (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)))) x) := by
  obtain ⟨S, hS⟩ := exists_finset_mem_iff_dvd_map φ (poly p) (ne_zero p)
  exact ⟨S, hS,
    milnorKNormRing_ratFunc_map_eq_sum_coefficientFactors_of_normal_prime φ p hp S hS⟩

end Stacks.Chow
