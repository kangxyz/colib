/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentFinite
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Finiteness of interpolated Laurent power cuts

The numerator after clearing the denominators of the interpolation between two
Laurent power ratios gives a finite cut over the coefficient ring. The bound on
both exponents is independent of the interpolation parameter.

This is the affine support estimate for Remark 4.2 of Voevodsky's
cancellation theorem, Documenta Mathematica Extra Volume Suslin (2010).
-/

@[expose] public section

noncomputable section

open scoped Polynomial
open Polynomial

namespace LaurentPolynomial

universe u v

variable {R : Type u} [CommRing R]

/-- Clear the negative Laurent powers in the lower coefficients by one common power. -/
private theorem exists_toLaurent_coeff_mul_T (p : (LaurentPolynomial R)[X]) :
    ∃ (m : ℕ) (c : ℕ → R[X]), ∀ i < p.natDegree,
      Polynomial.toLaurent (c i) = p.coeff i * T (m : ℤ) := by
  classical
  choose d f hf using fun i : ℕ => (p.coeff i).exists_T_pow
  let m := (Finset.range p.natDegree).sup d
  refine ⟨m, fun i => f i * X ^ (m - d i), ?_⟩
  intro i hi
  have hd : d i ≤ m := Finset.le_sup (f := d) (Finset.mem_range.mpr hi)
  rw [map_mul, hf i, toLaurent_X_pow, mul_T_assoc, Int.ofNat_sub hd, add_sub_cancel]

/-- A monic Laurent relation for `z` gives a monic relation for the image of `T`
when that image satisfies `a = b * z` with sufficient degree gap. -/
private theorem exists_isIntegral_of_monic_eval₂_relation [Nontrivial R]
    (p : (LaurentPolynomial R)[X]) (hp : p.Monic) :
    ∃ N : ℕ, ∀ {D : Type v} [CommRing D] [Algebra R D]
      (f : LaurentPolynomial R →ₐ[R] D) (z : D) (a b : R[X]), a.Monic →
      b.natDegree + N ≤ a.natDegree → Polynomial.eval₂ f.toRingHom z p = 0 →
      aeval (f (T 1)) a = aeval (f (T 1)) b * z → IsIntegral R (f (T 1)) := by
  obtain ⟨m, c, hc⟩ := exists_toLaurent_coeff_mul_T p
  let d := p.natDegree
  let s := Finset.range d
  let N := s.sup (fun i => (c i).natDegree) + 1
  refine ⟨N, ?_⟩
  intro D _ _ f z a b ha hgap hz hab
  let v := f (T 1)
  let L : R[X] := X ^ m * a ^ d
  let Q : R[X] := ∑ i ∈ s, c i * a ^ i * b ^ (d - i)
  have hL : L.Monic := (monic_X_pow m).mul (ha.pow d)
  have hLdeg : L.degree = (d * a.natDegree + m : ℕ) := by
    rw [degree_eq_natDegree hL.ne_zero]
    dsimp only [L]
    rw [natDegree_X_pow_mul m (ha.pow d).ne_zero, ha.natDegree_pow]
  have hQ : Q.degree < L.degree := by
    rw [hLdeg]
    refine (degree_sum_le s _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 ?_)
    intro i hi
    have hci : (c i).natDegree < N :=
      Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (c j).natDegree) hi)
    have hid := Finset.mem_range.mp hi
    have hpos : 1 ≤ d - i := by omega
    have hmul := Nat.mul_le_mul_left (d - i) hgap
    rw [Nat.mul_add] at hmul
    have hNmul := Nat.mul_le_mul_right N hpos
    rw [Nat.one_mul] at hNmul
    have hsum : i * a.natDegree + (d - i) * a.natDegree = d * a.natDegree := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hid.le]
    calc
      (c i * a ^ i * b ^ (d - i)).degree ≤
          ((c i * a ^ i * b ^ (d - i)).natDegree : WithBot ℕ) := degree_le_natDegree
      _ ≤ ((c i).natDegree + i * a.natDegree + (d - i) * b.natDegree : ℕ) := by
        exact_mod_cast natDegree_mul_le.trans
          (Nat.add_le_add (natDegree_mul_le.trans
            (Nat.add_le_add_left (natDegree_pow_le (p := a)) _)) (natDegree_pow_le (p := b)))
      _ < (d * a.natDegree + m : ℕ) := by exact_mod_cast (show
        (c i).natDegree + i * a.natDegree + (d - i) * b.natDegree < d * a.natDegree + m by omega)
  have hroot : z ^ d + (∑ i ∈ s, f (p.coeff i) * z ^ i) = 0 := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree,
      map_one, one_mul] at hz
    rw [add_comm]
    exact hz
  let av := aeval v a
  let bv := aeval v b
  have hrel : av = bv * z := hab
  have hhom : av ^ d + (∑ i ∈ s, f (p.coeff i) * av ^ i * bv ^ (d - i)) = 0 := by
    calc
      _ = bv ^ d * (z ^ d + ∑ i ∈ s, f (p.coeff i) * z ^ i) := by
        simp only [hrel, mul_pow, mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hpow : bv ^ d = bv ^ i * bv ^ (d - i) := by
          rw [← pow_add, Nat.add_sub_of_le (Finset.mem_range.mp hi).le]
        rw [hpow]
        ac_rfl
      _ = 0 := by rw [hroot, mul_zero]
  have hmap : (f.comp Polynomial.toLaurentAlg) = aeval v := by
    apply Polynomial.algHom_ext
    simp [v]
  have hcEval (i : ℕ) (hi : i ∈ s) :
      aeval v (c i) = f (p.coeff i) * v ^ m := by
    rw [← hmap, AlgHom.comp_apply, Polynomial.toLaurentAlg_apply,
      hc i (Finset.mem_range.mp hi), map_mul, ← Polynomial.toLaurent_X_pow, map_pow,
      Polynomial.toLaurent_X, map_pow]
  refine ⟨L + Q, hL.add_of_left hQ, ?_⟩
  have hQEval : aeval v Q = ∑ i ∈ s, f (p.coeff i) * av ^ i * bv ^ (d - i) * v ^ m := by
    dsimp only [Q]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [map_mul, map_pow, hcEval i hi, av, bv]
    ac_rfl
  have h := congrArg (fun x : D => x * v ^ m) hhom
  rw [add_mul, Finset.sum_mul, zero_mul, mul_comm (av ^ d)] at h
  change aeval v (L + Q) = 0
  simpa only [L, av, map_add, map_mul, map_pow, aeval_X, hQEval] using h

private def powerCutFamilyA (m n : ℕ) (s : R) : R[X] :=
  X ^ (m + n) - (Polynomial.C (1 - s) * X ^ m + Polynomial.C s * X ^ n)

private def powerCutFamilyB (m n : ℕ) (s : R) : R[X] :=
  Polynomial.C s * X ^ m + Polynomial.C (1 - s) * X ^ n - 1

private theorem powerCutFamilyA_monic_natDegree [Nontrivial R] {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (s : R) :
    (powerCutFamilyA m n s).Monic ∧ (powerCutFamilyA m n s).natDegree = m + n := by
  let p : R[X] := Polynomial.C (1 - s) * X ^ m + Polynomial.C s * X ^ n
  have hp : p.natDegree ≤ max m n := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le m).trans (le_max_left _ _))
    · exact (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le n).trans (le_max_right _ _))
  have hlt : (-p).natDegree < (X ^ (m + n) : R[X]).natDegree := by
    rw [natDegree_neg, natDegree_X_pow]
    exact hp.trans_lt (max_lt (by omega) (by omega))
  change (X ^ (m + n) - p).Monic ∧ (X ^ (m + n) - p).natDegree = m + n
  rw [sub_eq_add_neg]
  exact ⟨monic_X_pow_add (by simpa only [degree_X_pow] using degree_lt_degree hlt),
    (natDegree_add_eq_left_of_natDegree_lt hlt).trans (natDegree_X_pow _)⟩

private theorem powerCutFamilyB_natDegree_le (m n : ℕ) (s : R) :
    (powerCutFamilyB m n s).natDegree ≤ max m n := by
  unfold powerCutFamilyB
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le m).trans (le_max_left _ _))
    · exact (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le n).trans (le_max_right _ _))
  · rw [natDegree_one]
    exact Nat.zero_le _

variable {D : Type v} [CommRing D] [Algebra R D]

private theorem powerCutFamily_aeval_reciprocal (v : Dˣ) (m n : ℕ) (s : R) :
    ((v⁻¹ : Dˣ) : D) ^ (m + n) * aeval (v : D) (powerCutFamilyA m n s) =
      -aeval ((v⁻¹ : Dˣ) : D) (powerCutFamilyB m n s) ∧
    ((v⁻¹ : Dˣ) : D) ^ (m + n) * aeval (v : D) (powerCutFamilyB m n s) =
      -aeval ((v⁻¹ : Dˣ) : D) (powerCutFamilyA m n s) := by
  let i := ((v⁻¹ : Dˣ) : D)
  let c := i ^ (m + n)
  have hinv (j : ℕ) : i ^ j * (v : D) ^ j = 1 := by
    rw [← mul_pow]
    change (((v⁻¹ : Dˣ) : D) * (v : D)) ^ j = 1
    rw [Units.inv_mul, one_pow]
  have htop : c * (v : D) ^ (m + n) = 1 := hinv _
  have hm : c * (v : D) ^ m = i ^ n := by
    dsimp only [c]
    rw [pow_add, mul_comm (i ^ m) (i ^ n), mul_assoc, hinv, mul_one]
  have hn : c * (v : D) ^ n = i ^ m := by
    dsimp only [c]
    rw [pow_add, mul_assoc, hinv, mul_one]
  constructor
  · calc
      c * aeval (v : D) (powerCutFamilyA m n s) =
          c * (v : D) ^ (m + n) -
            (algebraMap R D (1 - s) * (c * (v : D) ^ m) +
              algebraMap R D s * (c * (v : D) ^ n)) := by
        simp only [powerCutFamilyA, map_sub, map_add, map_mul, aeval_C, aeval_X_pow]
        ring
      _ = -aeval i (powerCutFamilyB m n s) := by
        rw [htop, hm, hn]
        simp only [powerCutFamilyB, map_sub, map_add, map_mul, map_one, aeval_C, aeval_X_pow]
        ring
  · calc
      c * aeval (v : D) (powerCutFamilyB m n s) =
          algebraMap R D s * (c * (v : D) ^ m) +
            algebraMap R D (1 - s) * (c * (v : D) ^ n) - c := by
        simp only [powerCutFamilyB, map_sub, map_add, map_mul, map_one, aeval_C, aeval_X_pow]
        ring
      _ = -aeval i (powerCutFamilyA m n s) := by
        rw [hm, hn]
        simp only [powerCutFamilyA, map_sub, map_add, map_mul, aeval_C, aeval_X_pow]
        dsimp only [c]
        ring

/-- The numerator obtained by clearing the two denominators of the interpolated
Laurent power ratio. The two indices are the actual exponents. -/
def powerCutFamilyEquation (R : Type u) {B : Type v} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra (LaurentPolynomial R) B] (u : Bˣ) (m n : ℕ) (s : R) : B :=
  let tₘ := algebraMap (LaurentPolynomial R) B (T (m : ℤ))
  let tₙ := algebraMap (LaurentPolynomial R) B (T (n : ℤ))
  let b := algebraMap R B s
  b * (tₘ - 1) * (tₙ - (u : B)) + (1 - b) * (tₙ - 1) * (tₘ - (u : B))

/-- The interpolated Laurent power cut is finite over the coefficient ring for a
single bound on both exponents and all coefficients of the interpolation. -/
theorem exists_moduleFinite_quotient_span_powerCutFamilyEquation
    (R : Type u) {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra (LaurentPolynomial R) B] [IsScalarTower R (LaurentPolynomial R) B]
    [Module.Finite (LaurentPolynomial R) B] (u : Bˣ) :
    ∃ N : ℕ, ∀ (m n : ℕ), N ≤ m → N ≤ n → ∀ s : R,
      Module.Finite R (B ⧸ Ideal.span {powerCutFamilyEquation R u m n s}) := by
  obtain hR | hR := subsingleton_or_nontrivial R
  · refine ⟨1, ?_⟩
    intro m n _ _ s
    let : Subsingleton (B ⧸ Ideal.span {powerCutFamilyEquation R u m n s}) :=
      Module.subsingleton R _
    infer_instance
  obtain ⟨p, hp, hpu⟩ := IsIntegral.of_finite (LaurentPolynomial R) (u : B)
  obtain ⟨r, hr, hru⟩ := IsIntegral.of_finite (LaurentPolynomial R) ((u⁻¹ : Bˣ) : B)
  change aeval (u : B) p = 0 at hpu
  change aeval ((u⁻¹ : Bˣ) : B) r = 0 at hru
  let rev := LaurentPolynomial.invert (R := R)
  obtain ⟨N, hN⟩ := exists_isIntegral_of_monic_eval₂_relation.{u, v} p hp
  obtain ⟨M, hM⟩ := exists_isIntegral_of_monic_eval₂_relation.{u, v}
    (r.map rev.toRingHom) (hr.map rev.toRingHom)
  refine ⟨max 1 (max N M), ?_⟩
  intro m n hm hn s
  let I := Ideal.span {powerCutFamilyEquation R u m n s}
  let Q := B ⧸ I
  let q := Ideal.Quotient.mkₐ (LaurentPolynomial R) I
  let f := IsScalarTower.toAlgHom R (LaurentPolynomial R) Q
  let v : Qˣ :=
    { val := f (T 1)
      inv := f (T (-1))
      val_inv := by rw [← map_mul, ← T_add, add_neg_cancel, T_zero, map_one]
      inv_val := by rw [← map_mul, ← T_add, neg_add_cancel, T_zero, map_one] }
  let a := powerCutFamilyA m n s
  let b := powerCutFamilyB m n s
  have h₁m : 1 ≤ m := (le_max_left _ _).trans hm
  have h₁n : 1 ≤ n := (le_max_left _ _).trans hn
  have hNm : max N M ≤ m := (le_max_right _ _).trans hm
  have hNn : max N M ≤ n := (le_max_right _ _).trans hn
  obtain ⟨ha, hadeg⟩ := powerCutFamilyA_monic_natDegree h₁m h₁n s
  have hbdeg := powerCutFamilyB_natDegree_le m n s
  have hgap (i : ℕ) (hi : i ≤ max N M) : b.natDegree + i ≤ a.natDegree := by
    change (powerCutFamilyB m n s).natDegree + i ≤ (powerCutFamilyA m n s).natDegree
    rw [hadeg]
    omega
  have hqT (j : ℕ) : q (algebraMap (LaurentPolynomial R) B (T (j : ℤ))) = (v : Q) ^ j := by
    change f (T (j : ℤ)) = (v : Q) ^ j
    rw [show (T (j : ℤ) : LaurentPolynomial R) = T 1 ^ j by simp, map_pow]
  have hqC (r : R) : q (algebraMap R B r) = algebraMap R Q r := by
    change algebraMap B Q (algebraMap R B r) = algebraMap R Q r
    exact (IsScalarTower.algebraMap_apply R B Q r).symm
  have hzero : q (powerCutFamilyEquation R u m n s) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hab : aeval (v : Q) a = aeval (v : Q) b * q (u : B) := by
    apply sub_eq_zero.mp
    calc
      _ = q (powerCutFamilyEquation R u m n s) := by
        simp only [a, b, powerCutFamilyA, powerCutFamilyB, powerCutFamilyEquation,
          map_sub, map_add, map_mul, map_one, aeval_C, aeval_X_pow, hqT, hqC]
        rw [pow_add]
        ring
      _ = 0 := hzero
  obtain ⟨hrecA, hrecB⟩ := powerCutFamily_aeval_reciprocal v m n s
  have hscaled := congrArg (fun z : Q => ((v⁻¹ : Qˣ) : Q) ^ (m + n) * z) hab
  change ((v⁻¹ : Qˣ) : Q) ^ (m + n) * aeval (v : Q) (powerCutFamilyA m n s) =
    ((v⁻¹ : Qˣ) : Q) ^ (m + n) * (aeval (v : Q) (powerCutFamilyB m n s) * q (u : B))
    at hscaled
  rw [← mul_assoc, hrecA, hrecB, neg_mul, neg_inj] at hscaled
  have habInv : aeval ((v⁻¹ : Qˣ) : Q) a =
      aeval ((v⁻¹ : Qˣ) : Q) b * q ((u⁻¹ : Bˣ) : B) := by
    change aeval ((v⁻¹ : Qˣ) : Q) (powerCutFamilyA m n s) =
      aeval ((v⁻¹ : Qˣ) : Q) (powerCutFamilyB m n s) * q ((u⁻¹ : Bˣ) : B)
    rw [hscaled, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have hEval : Polynomial.eval₂ f.toRingHom (q (u : B)) p = 0 := by
    change aeval (q (u : B)) p = 0
    rw [aeval_algHom_apply, hpu, map_zero]
  let fInv := f.comp rev.toAlgHom
  have hComp : fInv.toRingHom.comp rev.toRingHom = f.toRingHom := by
    apply RingHom.ext
    intro z
    change f (rev (rev z)) = f z
    exact congrArg f (LaurentPolynomial.involutive_invert z)
  have hEvalInv :
      Polynomial.eval₂ fInv.toRingHom (q ((u⁻¹ : Bˣ) : B)) (r.map rev.toRingHom) = 0 := by
    rw [Polynomial.eval₂_map, hComp]
    change aeval (q ((u⁻¹ : Bˣ) : B)) r = 0
    rw [aeval_algHom_apply, hru, map_zero]
  have hTinverse : fInv (T 1) = ((v⁻¹ : Qˣ) : Q) := by
    change f (rev (T 1)) = f (T (-1))
    rw [LaurentPolynomial.invert_T]
  have hIntegral : IsIntegral R (f (T 1)) :=
    hN f (q (u : B)) a b ha (hgap _ (le_max_left _ _)) hEval hab
  have hIntegralInv : IsIntegral R (f (T (-1))) := by
    change IsIntegral R ((v⁻¹ : Qˣ) : Q)
    rw [← hTinverse]
    exact hM fInv (q ((u⁻¹ : Bˣ) : B)) a b ha (hgap _ (le_max_right _ _)) hEvalInv
      (by rw [hTinverse]; exact habInv)
  let : Module.Finite (LaurentPolynomial R) Q :=
    Module.Finite.of_surjective q.toLinearMap Ideal.Quotient.mk_surjective
  exact moduleFinite_of_integral_T_and_T_neg hIntegral hIntegralInv

/-- The numerator cut at a positive exponent is finite over the coefficient ring. -/
theorem moduleFinite_quotient_span_T_sub_one (R : Type u) {B : Type v}
    [CommRing R] [CommRing B] [Algebra R B] [Algebra (LaurentPolynomial R) B]
    [IsScalarTower R (LaurentPolynomial R) B] [Module.Finite (LaurentPolynomial R) B]
    {m : ℕ} (hm : 0 < m) :
    Module.Finite R (B ⧸ Ideal.span {algebraMap (LaurentPolynomial R) B (T (m : ℤ)) - 1}) := by
  let I : Ideal B := Ideal.span {algebraMap (LaurentPolynomial R) B (T (m : ℤ)) - 1}
  let Q := B ⧸ I
  let q := Ideal.Quotient.mkₐ (LaurentPolynomial R) I
  let v := algebraMap (LaurentPolynomial R) Q (T 1)
  let w := algebraMap (LaurentPolynomial R) Q (T (-1))
  have hzero : q (algebraMap (LaurentPolynomial R) B (T (m : ℤ)) - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hv : v ^ m = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at hzero
    dsimp only [v]
    rw [← map_pow, T_pow, mul_one]
    exact hzero
  have hw : w ^ m = 1 := by
    calc
      w ^ m = v ^ m * w ^ m := by rw [hv, one_mul]
      _ = 1 := by
        dsimp only [v, w]
        rw [← mul_pow, ← map_mul, ← T_add, add_neg_cancel, T_zero, map_one, one_pow]
  let : Module.Finite (LaurentPolynomial R) Q :=
    Module.Finite.of_surjective q.toLinearMap Ideal.Quotient.mk_surjective
  exact moduleFinite_of_integral_T_and_T_neg
    (IsIntegral.of_pow hm (hv.symm ▸ isIntegral_one))
    (IsIntegral.of_pow hm (hw.symm ▸ isIntegral_one))

end LaurentPolynomial
