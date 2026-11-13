/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Finiteness of Laurent power cuts

In a finite algebra over a Laurent polynomial ring, the equation that a sufficiently
high power of the Laurent coordinate is a specified unit cuts out a finite algebra
over the original coefficient ring. Monic equations for the unit and its inverse give
monic equations for both directions of the Laurent coordinate on the cut.

This is an affine support estimate for the power cuts in Voevodsky's cancellation
theorem, Documenta Mathematica Extra Volume Suslin (2010), Lemma 4.1.
-/

@[expose] public section

open scoped Polynomial
open Polynomial

namespace LaurentPolynomial

universe u v

variable {R : Type u} {D : Type v} [CommRing R] [CommRing D] [Algebra R D]

private theorem exists_coefficients_toLaurent_mul_T (p : (LaurentPolynomial R)[X]) :
    ∃ (m : ℕ) (c : ℕ → R[X]), ∀ i < p.natDegree,
      Polynomial.toLaurent (c i) = p.coeff i * T (m : ℤ) := by
  classical
  choose d f hf using fun i : ℕ => (p.coeff i).exists_T_pow
  let m := (Finset.range p.natDegree).sup d
  refine ⟨m, fun i => f i * X ^ (m - d i), ?_⟩
  intro i hi
  have hd : d i ≤ m := Finset.le_sup (f := d) (Finset.mem_range.mpr hi)
  rw [map_mul, hf i, toLaurent_X_pow, mul_T_assoc, Int.ofNat_sub hd, add_sub_cancel]

private theorem exists_isIntegral_of_monic_eval₂_pow (p : (LaurentPolynomial R)[X])
    (hp : p.Monic) :
    ∃ N : ℕ, ∀ {D : Type v} [CommRing D] [Algebra R D] (v : Dˣ) (n : ℕ), N ≤ n →
      Polynomial.eval₂ (LaurentPolynomial.eval₂ (algebraMap R D) v) ((v : D) ^ n) p = 0 →
      IsIntegral R (v : D) := by
  obtain ⟨m, c, hc⟩ := exists_coefficients_toLaurent_mul_T p
  let s := Finset.range p.natDegree
  let N := s.sup (fun i => (c i).natDegree) + 1
  refine ⟨N, ?_⟩
  intro D _ _ v n hN h
  let e := LaurentPolynomial.eval₂ (algebraMap R D) v
  let q : R[X] := ∑ i ∈ s, c i * X ^ (n * i)
  have hq : q.degree < (n * p.natDegree + m : ℕ) := by
    refine (degree_sum_le s _).trans_lt ((Finset.sup_lt_iff ?_).2 ?_)
    · exact WithBot.bot_lt_coe _
    · intro i hi
      have hci : (c i).natDegree < n :=
        (Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (c j).natDegree) hi)).trans_le hN
      have hid := Finset.mem_range.mp hi
      calc
        (c i * X ^ (n * i)).degree ≤ ((c i * X ^ (n * i)).natDegree : WithBot ℕ) :=
          degree_le_natDegree
        _ ≤ ((c i).natDegree + n * i : ℕ) := by
          exact_mod_cast natDegree_mul_le.trans (Nat.add_le_add_left (natDegree_X_pow_le _) _)
        _ < (n * p.natDegree + m : ℕ) := by
          exact_mod_cast
            (calc
              (c i).natDegree + n * i < n * (i + 1) := by rw [Nat.mul_succ]; lia
              _ ≤ n * p.natDegree + m := by
                exact (Nat.mul_le_mul_left n hid).trans (Nat.le_add_right _ _))
  have he : (v : D) ^ (n * p.natDegree) +
      (∑ i ∈ s, e (p.coeff i) * (v : D) ^ (n * i)) = 0 := by
    change Polynomial.eval₂ e ((v : D) ^ n) p = 0 at h
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree,
      map_one, one_mul] at h
    simpa only [s, pow_mul, add_comm] using h
  have hcEval (i : ℕ) (hi : i ∈ s) :
      aeval (v : D) (c i) = e (p.coeff i) * (v : D) ^ m := by
    rw [Polynomial.aeval_def, ← LaurentPolynomial.eval₂_toLaurent,
      hc i (Finset.mem_range.mp hi), map_mul, LaurentPolynomial.eval₂_T_n]
  have hqEval : aeval (v : D) q =
      ∑ i ∈ s, e (p.coeff i) * (v : D) ^ (n * i) * (v : D) ^ m := by
    dsimp only [q]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_mul, hcEval i hi, aeval_X_pow]
    ac_rfl
  refine ⟨X ^ (n * p.natDegree + m) + q, monic_X_pow_add hq, ?_⟩
  have hm := congrArg (fun z : D => z * (v : D) ^ m) he
  rw [add_mul, Finset.sum_mul, zero_mul, ← pow_add] at hm
  change aeval (v : D) (X ^ (n * p.natDegree + m) + q) = 0
  rw [map_add, aeval_X_pow, hqEval]
  exact hm

private theorem eval₂_inv_comp_invert (v : Dˣ) :
    (LaurentPolynomial.eval₂ (algebraMap R D) v⁻¹).comp
        (LaurentPolynomial.invert : LaurentPolynomial R ≃ₐ[R] LaurentPolynomial R).toRingHom =
      LaurentPolynomial.eval₂ (algebraMap R D) v := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (X : R[X]))
  apply Polynomial.ringHom_ext
  · intro r
    simp [LaurentPolynomial.algebraMap_eq_toLaurent]
  · simp [LaurentPolynomial.algebraMap_eq_toLaurent]

private theorem eval₂_eq_algebraMap [Algebra (LaurentPolynomial R) D]
    [IsScalarTower R (LaurentPolynomial R) D] (v : Dˣ)
    (hv : (v : D) = algebraMap (LaurentPolynomial R) D (T 1)) :
    LaurentPolynomial.eval₂ (algebraMap R D) v = algebraMap (LaurentPolynomial R) D := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (X : R[X]))
  apply Polynomial.ringHom_ext
  · intro r
    change LaurentPolynomial.eval₂ (algebraMap R D) v (Polynomial.toLaurent (Polynomial.C r)) =
      algebraMap (LaurentPolynomial R) D (Polynomial.toLaurent (Polynomial.C r))
    rw [toLaurent_C, eval₂_C, LaurentPolynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply R (LaurentPolynomial R) D]
  · simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hv

private theorem moduleFinite_of_eval₂ [Algebra (LaurentPolynomial R) D]
    [IsScalarTower R (LaurentPolynomial R) D] [Module.Finite (LaurentPolynomial R) D]
    (v : Dˣ) (he : LaurentPolynomial.eval₂ (algebraMap R D) v =
      algebraMap (LaurentPolynomial R) D)
    (hv : IsIntegral R (v : D)) (hvi : IsIntegral R ((v⁻¹ : Dˣ) : D)) :
    Module.Finite R D := by
  let S := Algebra.adjoin R {(v : D), ((v⁻¹ : Dˣ) : D)}
  have hvS : (v : D) ∈ S := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hviS : ((v⁻¹ : Dˣ) : D) ∈ S :=
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hmem (f : LaurentPolynomial R) : LaurentPolynomial.eval₂ (algebraMap R D) v f ∈ S := by
    induction f using LaurentPolynomial.induction_on' with
    | add _ _ hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
    | C_mul_T j r =>
      obtain ⟨i, rfl | rfl⟩ := Int.eq_nat_or_neg j
      · rw [eval₂_C_mul_T_n]
        exact S.mul_mem (S.algebraMap_mem r) (S.pow_mem hvS i)
      · rw [eval₂_C_mul_T_neg_n]
        exact S.mul_mem (S.algebraMap_mem r) (S.pow_mem hviS i)
  let e : LaurentPolynomial R →ₐ[R] S :=
    (IsScalarTower.toAlgHom R (LaurentPolynomial R) D).codRestrict S fun f => by
      change algebraMap (LaurentPolynomial R) D f ∈ S
      rw [← he]
      exact hmem f
  let : Algebra (LaurentPolynomial R) S := e.toRingHom.toAlgebra
  let : IsScalarTower (LaurentPolynomial R) S D :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.Finite S D := Module.Finite.of_restrictScalars_finite (LaurentPolynomial R) S D
  let : Module.Finite R S := Algebra.finite_adjoin_of_finite_of_isIntegral
    ((Set.finite_singleton _).insert _) (by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact hv
      · simpa only [Set.mem_singleton_iff.mp hz] using hvi)
  exact Module.Finite.trans S D

/-- A high Laurent power cut by a unit in a finite algebra has finite coefficient module. -/
theorem exists_moduleFinite_quotient_span_T_sub_unit (R : Type u) {B : Type v}
    [CommRing R] [CommRing B] [Algebra R B] [Algebra (LaurentPolynomial R) B]
    [IsScalarTower R (LaurentPolynomial R) B] [Module.Finite (LaurentPolynomial R) B] (u : Bˣ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Module.Finite R
      (B ⧸ Ideal.span {algebraMap (LaurentPolynomial R) B (T (n : ℤ)) - (u : B)}) := by
  let I (n : ℕ) : Ideal B :=
    Ideal.span {algebraMap (LaurentPolynomial R) B (T (n : ℤ)) - (u : B)}
  obtain ⟨p, hp, hpu⟩ := IsIntegral.of_finite (LaurentPolynomial R) (u : B)
  obtain ⟨r, hr, hru⟩ := IsIntegral.of_finite (LaurentPolynomial R) ((u⁻¹ : Bˣ) : B)
  change aeval (u : B) p = 0 at hpu
  change aeval ((u⁻¹ : Bˣ) : B) r = 0 at hru
  let inv := (LaurentPolynomial.invert : LaurentPolynomial R ≃ₐ[R] LaurentPolynomial R).toRingHom
  -- The bounds use only the two chosen equations.
  obtain ⟨N, hN⟩ := exists_isIntegral_of_monic_eval₂_pow.{u, v} p hp
  obtain ⟨M, hM⟩ := exists_isIntegral_of_monic_eval₂_pow.{u, v} (r.map inv) (hr.map inv)
  refine ⟨max N M, ?_⟩
  intro n hn
  -- Both monic equations descend to the actual quotient.
  let Q := B ⧸ I n
  let q := Ideal.Quotient.mkₐ (LaurentPolynomial R) (I n)
  let v : Qˣ :=
    { val := algebraMap (LaurentPolynomial R) Q (T 1)
      inv := algebraMap (LaurentPolynomial R) Q (T (-1))
      val_inv := by rw [← map_mul, ← T_add, add_neg_cancel, T_zero, map_one]
      inv_val := by rw [← map_mul, ← T_add, neg_add_cancel, T_zero, map_one] }
  have hv : (v : Q) ^ n = q (u : B) := by
    have hzero : q (algebraMap (LaurentPolynomial R) B (T (n : ℤ)) - (u : B)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [map_sub, sub_eq_zero] at hzero
    change (algebraMap (LaurentPolynomial R) Q (T 1)) ^ n = _
    rw [← map_pow, T_pow, mul_one]
    exact hzero
  have hvUnits : v ^ n = Units.map q.toRingHom u := Units.ext hv
  have hvi : ((v⁻¹ : Qˣ) : Q) ^ n = q ((u⁻¹ : Bˣ) : B) := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hvUnits, ← map_inv]
    rfl
  have he := eval₂_eq_algebraMap (R := R) v rfl
  have hEval : Polynomial.eval₂ (LaurentPolynomial.eval₂ (algebraMap R Q) v)
      ((v : Q) ^ n) p = 0 := by
    rw [hv, he, ← aeval_def, aeval_algHom_apply, hpu, map_zero]
  have hEvalInv : Polynomial.eval₂ (LaurentPolynomial.eval₂ (algebraMap R Q) v⁻¹)
      (((v⁻¹ : Qˣ) : Q) ^ n) (r.map inv) = 0 := by
    rw [hvi, Polynomial.eval₂_map, eval₂_inv_comp_invert, he,
      ← aeval_def, aeval_algHom_apply, hru, map_zero]
  let : Module.Finite (LaurentPolynomial R) Q :=
    Module.Finite.of_surjective q.toLinearMap Ideal.Quotient.mk_surjective
  exact moduleFinite_of_eval₂ v he
    (hN v n ((le_max_left _ _).trans hn) hEval)
    (hM v⁻¹ n ((le_max_right _ _).trans hn) hEvalInv)

end LaurentPolynomial
