/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.SplitPolynomialCycle
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionMixed
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.SkewSymmetry
import Colib.RingTheory.Charpoly.Basic
import Colib.RingTheory.Norm.FiniteAlgebra
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases

/-!
# The Steinberg relation for the literal weight-two graph classes

The two full cubic endpoints give a bound over a field containing a cubic
root of unity. Corestriction along the whole cubic and quadratic root algebras
uses all residue degrees and local lengths, yielding the uniform bound
twelve. Applying mixed corestriction to one more whole root algebra removes
the annihilator in characteristic zero.

Adapted from `Motivic/Cohomology/WeightTwo/{SteinbergTorsion,SteinbergBound}.lean`
at `motivic_source_a6805c4`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry Polynomial
open scoped BigOperators TensorProduct

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalSteinbergBound

open DiagonalCycleSymbols DiagonalSkewSymmetry DiagonalCubicBoundary DiagonalSplitPolynomialCycle
open DiagonalCorestriction DiagonalCorestrictionMixed

variable {k : Type u} [Field k]

private theorem corestriction_graphSymbol_mixed
    {E : Type u} [Field E] [Algebra k E] [Module.Finite k E] (a : kˣ) (b : Eˣ) :
    corestriction (k := k) 2 (graphSymbol E 2 ![Units.map (algebraMap k E).toMonoidHom a, b]) =
      graphSymbol k 2 ![a, Units.map (Algebra.norm k) b] := by
  have hsrc : mixedTuple (k := k) 2 ![a, 1] 1 b =
      ![Units.map (algebraMap k E).toMonoidHom a, b] := by
    funext i
    fin_cases i <;> simp [mixedTuple]
  have htgt : Function.update ![a, (1 : kˣ)] 1 (Units.map (Algebra.norm k) b) =
      ![a, Units.map (Algebra.norm k) b] := by
    funext i
    fin_cases i <;> simp
  rw [← hsrc, corestriction_graphSymbol_varying, htgt]

section TorsionRemoval

variable (k : Type u) [Field k]

/-- Powers in the first coordinate give the corresponding repeated addition. -/
theorem graphSymbol_pow_left (a b : kˣ) (n : ℕ) :
    graphSymbol k 2 ![a ^ n, b] = n • graphSymbol k 2 ![a, b] := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    exact graphSymbol_one k 2 ![1, b] 0 rfl
  | succ n ih => rw [pow_succ, graphSymbol_mul_left, ih, succ_nsmul]

/-- Powers in the second coordinate give the corresponding repeated addition. -/
theorem graphSymbol_pow_right (a b : kˣ) (n : ℕ) :
    graphSymbol k 2 ![a, b ^ n] = n • graphSymbol k 2 ![a, b] := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    exact graphSymbol_one k 2 ![a, 1] 1 rfl
  | succ n ih => rw [pow_succ, graphSymbol_mul_right, ih, succ_nsmul]

/-- A product in the second coordinate adds the original graph classes. -/
theorem graphSymbol_prod_right {ι : Type*} (s : Finset ι) (a : kˣ) (b : ι → kˣ) :
    graphSymbol k 2 ![a, ∏ i ∈ s, b i] = ∑ i ∈ s, graphSymbol k 2 ![a, b i] := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact graphSymbol_one k 2 ![a, 1] 1 rfl
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, graphSymbol_mul_right, ih]

/-- The bound is uniform over all fields of characteristic zero in the given universe. -/
def UniversalSteinbergAnnihilator (n : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (a b : Fˣ),
    (b : F) = 1 - (a : F) → n • graphSymbol F 2 ![a, b] = 0

private theorem norm_one_sub_root {F : Type u} [Field F] (P : F[X]) (hP : P.Monic) :
    Algebra.norm F (1 - AdjoinRoot.root P) = P.eval 1 := by
  let pb := AdjoinRoot.powerBasis' hP
  let : Module.Free F (AdjoinRoot P) := hP.free_adjoinRoot
  let : Module.Finite F (AdjoinRoot P) := hP.finite_adjoinRoot
  have hchar : (Algebra.lmul F (AdjoinRoot P) (AdjoinRoot.root P)).charpoly = P := by
    rw [← LinearMap.charpoly_toMatrix _ pb.basis]
    change (Algebra.leftMulMatrix pb.basis pb.gen).charpoly = P
    exact (charpoly_leftMulMatrix pb).trans hP.minpoly_adjoinRoot
  have hnorm := Algebra.eval_charpoly_lmul_eq_norm (AdjoinRoot.root P) (1 : F)
  rw [hchar, map_one] at hnorm
  exact hnorm.symm

/-- A maximal quotient has the field structure supplied by its original maximal ideal. -/
local instance quotientField {R : Type u} [CommRing R] (q : MaximalSpectrum R) :
    Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal

/-- The full root algebra removes a positive factor from the uniform annihilator. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/WeightTwo/SteinbergTorsion.lean:72-128"
  "adaptation" "Whole root algebra and full residue-field norms remove the factor"]
theorem remove_positive_factor (m p : ℕ) (hp : 0 < p)
    (h : UniversalSteinbergAnnihilator.{u} (m * p)) :
    UniversalSteinbergAnnihilator.{u} m := by
  classical
  intro F _ _ a b hab
  let P : F[X] := (Polynomial.X : F[X]) ^ p - C (a : F)
  have hP : P.Monic := monic_X_pow_sub_C (a : F) hp.ne'
  let : Module.Finite F (AdjoinRoot P) := hP.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot P) := .of_finite F _
  let : Fintype (MaximalSpectrum (AdjoinRoot P)) := Fintype.ofFinite _
  let residueRoot (q : MaximalSpectrum (AdjoinRoot P)) : AdjoinRoot P ⧸ q.asIdeal :=
    Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root P)
  have hroot : (AdjoinRoot.root P) ^ p = AdjoinRoot.of P (a : F) := by
    have hr := AdjoinRoot.eval₂_root P
    simpa only [P, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] using hr
  have hpow (q : MaximalSpectrum (AdjoinRoot P)) :
      residueRoot q ^ p = algebraMap F (AdjoinRoot P ⧸ q.asIdeal) (a : F) := by
    change (Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root P)) ^ p = _
    rw [← map_pow, hroot]
    rfl
  have hroot_ne (q : MaximalSpectrum (AdjoinRoot P)) : residueRoot q ≠ 0 := by
    intro hx
    apply a.ne_zero
    apply (algebraMap F (AdjoinRoot P ⧸ q.asIdeal)).injective
    rw [map_zero, ← hpow q, hx, zero_pow hp.ne']
  have hcomp_ne (q : MaximalSpectrum (AdjoinRoot P)) : 1 - residueRoot q ≠ 0 := by
    intro hx
    have hx1 : residueRoot q = 1 := (sub_eq_zero.mp hx).symm
    have ha1 : (a : F) = 1 := by
      apply (algebraMap F (AdjoinRoot P ⧸ q.asIdeal)).injective
      rw [map_one, ← hpow q, hx1, one_pow]
    exact b.ne_zero (by rw [hab, ha1, sub_self])
  let rootUnit (q : MaximalSpectrum (AdjoinRoot P)) : (AdjoinRoot P ⧸ q.asIdeal)ˣ :=
    Units.mk0 (residueRoot q) (hroot_ne q)
  let complementUnit (q : MaximalSpectrum (AdjoinRoot P)) : (AdjoinRoot P ⧸ q.asIdeal)ˣ :=
    Units.mk0 (1 - residueRoot q) (hcomp_ne q)
  let localLength (q : MaximalSpectrum (AdjoinRoot P)) : ℕ :=
    (Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).toNat
  let N (q : MaximalSpectrum (AdjoinRoot P)) : Fˣ :=
    Units.map (Algebra.norm F) (complementUnit q)
  have hbranch (q : MaximalSpectrum (AdjoinRoot P)) :
      m • graphSymbol F 2 ![a, N q] = 0 := by
    let E := AdjoinRoot P ⧸ q.asIdeal
    let : CharZero E := Algebra.charZero_of_charZero F E
    have hpow_units : (rootUnit q) ^ p = Units.map (algebraMap F E).toMonoidHom a := by
      apply Units.ext
      exact hpow q
    have hE : m • graphSymbol E 2 ![Units.map (algebraMap F E).toMonoidHom a,
        complementUnit q] = 0 := by
      rw [← hpow_units, graphSymbol_pow_left, ← mul_smul]
      exact h E (rootUnit q) (complementUnit q) rfl
    have ht := congrArg (corestriction (k := F) (E := E) 2) hE
    simpa only [map_nsmul, corestriction_graphSymbol_mixed, map_zero] using ht
  have hnorm : (∏ q : MaximalSpectrum (AdjoinRoot P), N q ^ localLength q) = b := by
    apply Units.ext
    simp only [Units.coe_prod, Units.val_pow_eq_pow_val]
    change (∏ q : MaximalSpectrum (AdjoinRoot P),
      Algebra.norm F (1 - residueRoot q) ^ localLength q) = (b : F)
    have hprod := Algebra.norm_eq_prod_quotient_norm_pow_local_length
      (k := F) (1 - AdjoinRoot.root P)
    simp only [map_sub, map_one] at hprod
    calc
      _ = Algebra.norm F (1 - AdjoinRoot.root P) := hprod.symm
      _ = P.eval 1 := norm_one_sub_root P hP
      _ = (b : F) := by simpa only [P, eval_sub, eval_pow, eval_X, eval_C, one_pow] using hab.symm
  rw [← hnorm, graphSymbol_prod_right, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro q _
  rw [graphSymbol_pow_right, smul_comm m, hbranch q, smul_zero]

/-- A positive uniform bound and mixed norm descent give the complementary graph relation. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/WeightTwo/SteinbergTorsion.lean:130-138"
  "adaptation" "Remove the whole positive annihilator at once"]
theorem graphSymbol_eq_zero_of_universal_annihilator (n : ℕ) (hn : 0 < n)
    (h : UniversalSteinbergAnnihilator.{u} n)
    (F : Type u) [Field F] [CharZero F] (a b : Fˣ)
    (hab : (b : F) = 1 - (a : F)) : graphSymbol F 2 ![a, b] = 0 := by
  have h1 : UniversalSteinbergAnnihilator.{u} 1 :=
    remove_positive_factor 1 n hn (by simpa only [one_mul] using h)
  simpa only [one_smul] using h1 F a b hab


end TorsionRemoval

private theorem corestriction_graphSymbol_degree
    {E : Type u} [Field E] [Algebra k E] [Module.Finite k E] (a b : kˣ) :
    corestriction (k := k) 2 (graphSymbol E 2
      ![Units.map (algebraMap k E).toMonoidHom a, Units.map (algebraMap k E).toMonoidHom b]) =
        Module.finrank k E • graphSymbol k 2 ![a, b] := by
  have hnorm : Units.map (Algebra.norm k) (Units.map (algebraMap k E).toMonoidHom b) =
      b ^ Module.finrank k E := by
    apply Units.ext
    change Algebra.norm k (algebraMap k E (b : k)) = (b ^ Module.finrank k E : kˣ).val
    rw [Algebra.norm_algebraMap, Units.val_pow_eq_pow_val]
  rw [corestriction_graphSymbol_mixed, hnorm, graphSymbol_pow_right]

private theorem cube_eq_one_of_quadratic (w : k) (hw : w ^ 2 + w + 1 = 0) : w ^ 3 = 1 := by
  linear_combination (w - 1) * hw

private theorem complement_product (w a : k) (hw : w ^ 2 + w + 1 = 0) :
    (1 - a) * (1 - w * a) * (1 - w ^ 2 * a) = 1 - a ^ 3 := by
  have hw3 := cube_eq_one_of_quadratic w hw
  linear_combination (a ^ 2 - a) * hw + (a ^ 2 - a ^ 3) * hw3

private theorem cubicZero_factorization (w a : k) (hw : w ^ 2 + w + 1 = 0) :
    cubicZero a =
      (Polynomial.X - C a) * (Polynomial.X - C (w * a)) * (Polynomial.X - C (w ^ 2 * a)) := by
  have hw3 := cube_eq_one_of_quadratic w hw
  have hC := congrArg (C : k →+* k[X]) hw
  have hC3 := congrArg (C : k →+* k[X]) hw3
  simp only [map_add, map_pow, map_one, map_zero] at hC hC3
  simp only [cubicZero, map_mul, map_pow]
  linear_combination (C a * Polynomial.X ^ 2 - C a ^ 2 * Polynomial.X) * hC +
    (C a ^ 3 - C a ^ 2 * Polynomial.X) * hC3

private theorem cubicOne_factorization (w a : k) (hw : w ^ 2 + w + 1 = 0) :
    cubicOne a =
      (Polynomial.X - C (a ^ 3)) * (Polynomial.X - C (-w)) *
        (Polynomial.X - C (-(w ^ 2))) := by
  have hw3 := cube_eq_one_of_quadratic w hw
  have hC := congrArg (C : k →+* k[X]) hw
  have hC3 := congrArg (C : k →+* k[X]) hw3
  simp only [map_add, map_pow, map_one, map_zero] at hC hC3
  simp only [cubicOne, map_neg, map_pow]
  linear_combination -(Polynomial.X - C a ^ 3) * Polynomial.X * hC -
    (Polynomial.X - C a ^ 3) * hC3

/-- The complete cubic endpoints give the three original complementary graph classes. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/WeightTwo/SteinbergBound.lean:49-106"
  "adaptation" "Both original split endpoints, with the quadratic graphs canceled by skew symmetry"]
theorem cubic_symbol_relation (w a b₀ b₁ b₂ c : kˣ)
    (hw : (w : k) ^ 2 + (w : k) + 1 = 0)
    (hb₀ : (b₀ : k) = 1 - (a : k))
    (hb₁ : (b₁ : k) = 1 - (w * a : kˣ))
    (hb₂ : (b₂ : k) = 1 - (w ^ 2 * a : kˣ))
    (hc : (c : k) = 1 - (a : k) ^ 3) :
    graphSymbol k 2 ![a, b₀] + graphSymbol k 2 ![w * a, b₁] +
      graphSymbol k 2 ![w ^ 2 * a, b₂] = graphSymbol k 2 ![a ^ 3, c] := by
  have ha3 : (a : k) ^ 3 ≠ 1 := by
    intro h
    apply c.ne_zero
    rw [hc, h, sub_self]
  have hzero := cycleClass_eq_three_graphSymbol_of_factorization (cubicZero (a : k))
    (cubicZero_monic _) (cubicZero_constant_isUnit _ a.ne_zero)
    (cubicZero_eval_one_isUnit _ ha3) a b₀ (w * a) b₁ (w ^ 2 * a) b₂
    (by simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using
      cubicZero_factorization (w : k) (a : k) hw) hb₀ hb₁ hb₂
  have hneg₁ : (-(w ^ 2) : kˣ) = 1 - ((-w : kˣ) : k) := by
    simp only [Units.val_neg, Units.val_pow_eq_pow_val]
    linear_combination -hw
  have hneg₂ : ((-w : kˣ) : k) = 1 - ((-(w ^ 2) : kˣ) : k) := by
    simp only [Units.val_neg, Units.val_pow_eq_pow_val]
    linear_combination -hw
  have hone := cycleClass_eq_three_graphSymbol_of_factorization (cubicOne (a : k))
    (cubicOne_monic _) (cubicOne_constant_isUnit _ a.ne_zero)
    (cubicOne_eval_one_isUnit _ ha3) (a ^ 3) c (-w) (-(w ^ 2)) (-(w ^ 2)) (-w)
    (by simpa only [Units.val_pow_eq_pow_val, Units.val_neg] using
      cubicOne_factorization (w : k) (a : k) hw) hc hneg₁ hneg₂
  have h := hzero.symm.trans ((cubic_cycleClass_endpoints (a : k) a.ne_zero ha3).trans hone)
  simpa only [add_assoc, graphSymbol_add_swap, add_zero] using h

/-- A quadratic root of unity gives annihilation by two for complementary cube symbols. -/
theorem two_nsmul_cube_symbol (w a c : kˣ)
    (hw : (w : k) ^ 2 + (w : k) + 1 = 0) (hc : (c : k) = 1 - (a : k) ^ 3) :
    2 • graphSymbol k 2 ![a ^ 3, c] = 0 := by
  have hprod := complement_product (w : k) (a : k) hw
  have hp : (1 - (a : k)) * (1 - (w : k) * (a : k)) *
      (1 - (w : k) ^ 2 * (a : k)) ≠ 0 := by
    rw [hprod, ← hc]
    exact c.ne_zero
  obtain ⟨⟨h₀, h₁⟩, h₂⟩ := (mul_ne_zero_iff.mp hp).imp_left mul_ne_zero_iff.mp
  let b₀ : kˣ := Units.mk0 _ h₀
  let b₁ : kˣ := Units.mk0 _ h₁
  let b₂ : kˣ := Units.mk0 _ h₂
  have h := cubic_symbol_relation w a b₀ b₁ b₂ c hw rfl rfl rfl hc
  have hw3 : w ^ 3 = 1 := Units.ext (cube_eq_one_of_quadratic (w : k) hw)
  have hwa : (w * a) ^ 3 = a ^ 3 := by rw [mul_pow, hw3, one_mul]
  have hw2a : (w ^ 2 * a) ^ 3 = a ^ 3 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm 2 3, pow_mul, hw3, one_pow, one_mul]
  have hb : b₀ * b₁ * b₂ = c := Units.ext (hprod.trans hc.symm)
  have hscaled := congrArg (fun x => (3 : ℕ) • x) h
  rw [smul_add, smul_add, ← graphSymbol_pow_left, ← graphSymbol_pow_left,
    ← graphSymbol_pow_left, hwa, hw2a, ← graphSymbol_mul_right,
    ← graphSymbol_mul_right, hb] at hscaled
  have he : graphSymbol k 2 ![a ^ 3, c] + 2 • graphSymbol k 2 ![a ^ 3, c] =
      graphSymbol k 2 ![a ^ 3, c] + 0 := by
    simpa only [show 3 = 2 + 1 from rfl, succ_nsmul, add_zero, zero_add, zero_smul,
      add_comm] using hscaled.symm
  exact add_left_cancel he

local instance quotientFieldForBound {R : Type u} [CommRing R] (q : MaximalSpectrum R) :
    Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal

private theorem sum_local_length_mul_finrank_eq_natDegree
    (p : k[X]) (hp : p.Monic) [Fintype (MaximalSpectrum (AdjoinRoot p))] :
    ∑ q : MaximalSpectrum (AdjoinRoot p),
      (Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat * Module.finrank k (AdjoinRoot p ⧸ q.asIdeal) =
        p.natDegree := by
  let : Module.Finite k (AdjoinRoot p) := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  have h := Module.finiteAlgebra_length_eq_sum_tensor k (AdjoinRoot p)
    (M := AdjoinRoot p) Module.length_ne_top
  have hlocal (q : MaximalSpectrum (AdjoinRoot p)) :
      Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[AdjoinRoot p] AdjoinRoot p) =
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (TensorProduct.AlgebraTensorModule.rid (AdjoinRoot p)
      (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).length_eq
  have hdeg (q : MaximalSpectrum (AdjoinRoot p)) :
      (Module.finiteAlgebraResidueDegree k (AdjoinRoot p) q : ℕ∞) =
        (Module.finrank k (AdjoinRoot p ⧸ q.asIdeal) : ℕ∞) := by
    rw [← Module.finiteAlgebra_residue_length k (AdjoinRoot p) q, Module.length_eq_finrank]
  have hn (q : MaximalSpectrum (AdjoinRoot p)) :
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℕ∞) =
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) :=
    ENat.natCast_toNat (Algebra.local_length_ne_top_of_finite (k := k) q)
  have hdim : Module.finrank k (AdjoinRoot p) = p.natDegree := (AdjoinRoot.powerBasis' hp).finrank
  apply ENat.natCast_inj.mp
  push_cast
  simpa only [Module.length_eq_finrank, hlocal, hdeg, hn, hdim] using h.symm

/-- Annihilators on all original branches descend with the full degree of the root algebra. -/
theorem polynomial_annihilator_descent (p : k[X]) (hp : p.Monic) (n : ℕ) (a b : kˣ)
    (h : ∀ q : MaximalSpectrum (AdjoinRoot p),
      n • graphSymbol (AdjoinRoot p ⧸ q.asIdeal) 2
        ![Units.map (algebraMap k (AdjoinRoot p ⧸ q.asIdeal)).toMonoidHom a,
          Units.map (algebraMap k (AdjoinRoot p ⧸ q.asIdeal)).toMonoidHom b] = 0) :
    (n * p.natDegree) • graphSymbol k 2 ![a, b] = 0 := by
  classical
  let : Module.Finite k (AdjoinRoot p) := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  have hbranch (q : MaximalSpectrum (AdjoinRoot p)) :
      n • (Module.finrank k (AdjoinRoot p ⧸ q.asIdeal) • graphSymbol k 2 ![a, b]) = 0 := by
    have ht := congrArg (corestriction (k := k) (E := AdjoinRoot p ⧸ q.asIdeal) 2) (h q)
    simpa only [map_nsmul, corestriction_graphSymbol_degree, map_zero] using ht
  rw [← sum_local_length_mul_finrank_eq_natDegree p hp, mul_smul,
    Finset.sum_smul, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro q _
  rw [mul_smul, smul_comm n, hbranch q, smul_zero]

private def residueRootUnit (p : k[X]) (h0 : IsUnit (p.coeff 0))
    (q : MaximalSpectrum (AdjoinRoot p)) : (AdjoinRoot p ⧸ q.asIdeal)ˣ :=
  Units.map (Ideal.Quotient.mk q.asIdeal).toMonoidHom (AdjoinRoot.rootUnit p h0)

/-- The cubic root algebra gives annihilation by six over a field with the quadratic root. -/
theorem six_nsmul_symbol_of_quadratic_root (w a b : kˣ)
    (hw : (w : k) ^ 2 + (w : k) + 1 = 0) (hab : (b : k) = 1 - (a : k)) :
    6 • graphSymbol k 2 ![a, b] = 0 := by
  let P : k[X] := Polynomial.X ^ 3 - C (a : k)
  have hP : P.Monic := monic_X_pow_sub_C (a : k) (by decide)
  have h0 : IsUnit (P.coeff 0) := by
    rw [coeff_zero_eq_eval_zero]
    simpa only [P, eval_sub, eval_pow, eval_X, eval_C, zero_pow (by decide : 3 ≠ 0),
      zero_sub] using a.isUnit.neg
  have hroot : (AdjoinRoot.root P) ^ 3 = AdjoinRoot.of P (a : k) := by
    have hr := AdjoinRoot.eval₂_root P
    simpa only [P, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] using hr
  have hd : P.natDegree = 3 := by
    dsimp only [P]
    compute_degree!
  have h := polynomial_annihilator_descent P hP 2 a b (fun q => ?_)
  · simpa only [hd] using h
  let E := AdjoinRoot P ⧸ q.asIdeal
  let φ := algebraMap k E
  have hwE : (Units.map φ.toMonoidHom w : E) ^ 2 +
      (Units.map φ.toMonoidHom w : E) + 1 = 0 := by
    change φ (w : k) ^ 2 + φ (w : k) + 1 = 0
    simpa only [map_add, map_pow, map_one, map_zero] using congrArg φ hw
  have hpow : (residueRootUnit P h0 q) ^ 3 = Units.map φ.toMonoidHom a := by
    apply Units.ext
    change (Ideal.Quotient.mk q.asIdeal (AdjoinRoot.rootUnit P h0)) ^ 3 = φ (a : k)
    rw [AdjoinRoot.rootUnit_val, ← map_pow, hroot]
    rfl
  have hc : (Units.map φ.toMonoidHom b : E) = 1 - (residueRootUnit P h0 q : E) ^ 3 := by
    change φ (b : k) = 1 - (residueRootUnit P h0 q : E) ^ 3
    rw [← Units.val_pow_eq_pow_val, hpow]
    change φ (b : k) = 1 - φ (a : k)
    rw [hab, map_sub, map_one]
  have he := two_nsmul_cube_symbol (Units.map φ.toMonoidHom w)
    (residueRootUnit P h0 q) (Units.map φ.toMonoidHom b) hwE hc
  simpa only [hpow] using he

/-- The whole quadratic quotient gives the uniform integral bound twelve. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/WeightTwo/SteinbergBound.lean:108-236"
  "adaptation" "The original cubic and quadratic descent retains all branch degrees"]
theorem twelve_nsmul_graphSymbol (a b : kˣ) (hab : (b : k) = 1 - (a : k)) :
    12 • graphSymbol k 2 ![a, b] = 0 := by
  let P : k[X] := Polynomial.X ^ 2 + Polynomial.X + 1
  have hP : P.Monic := by
    dsimp only [P]
    monicity!
  have h0 : IsUnit (P.coeff 0) := by
    rw [coeff_zero_eq_eval_zero]
    simp only [P, eval_add, eval_pow, eval_X, eval_one, zero_pow (by decide : 2 ≠ 0), zero_add]
    exact isUnit_one
  have hd : P.natDegree = 2 := by
    dsimp only [P]
    compute_degree!
  have hroot : (AdjoinRoot.root P) ^ 2 + AdjoinRoot.root P + 1 = 0 := by
    have hr := AdjoinRoot.eval₂_root P
    simpa only [P, eval₂_add, eval₂_pow, eval₂_X, eval₂_one] using hr
  have h := polynomial_annihilator_descent P hP 6 a b (fun q => ?_)
  · simpa only [hd] using h
  let E := AdjoinRoot P ⧸ q.asIdeal
  let φ := algebraMap k E
  let w := residueRootUnit P h0 q
  have hw : (w : E) ^ 2 + (w : E) + 1 = 0 := by
    have he := congrArg (Ideal.Quotient.mk q.asIdeal) hroot
    change (Ideal.Quotient.mk q.asIdeal (AdjoinRoot.rootUnit P h0)) ^ 2 +
      Ideal.Quotient.mk q.asIdeal (AdjoinRoot.rootUnit P h0) + 1 = 0
    rw [AdjoinRoot.rootUnit_val]
    simpa only [map_add, map_pow, map_one, map_zero] using he
  apply six_nsmul_symbol_of_quadratic_root w _ _ hw
  change φ (b : k) = 1 - φ (a : k)
  rw [hab, map_sub, map_one]

/-- The bound is uniform over all fields in the torsion-removal argument. -/
theorem universalSteinbergAnnihilator_twelve : UniversalSteinbergAnnihilator.{u} 12 := by
  intro F _ _ a b hab
  exact twelve_nsmul_graphSymbol a b hab

/-- Complementary units have zero actual weight-two graph class in characteristic zero. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/WeightTwo/SteinbergBound.lean:238-243"
  "adaptation" "Integral Steinberg relation for the genuine rational graph class"]
theorem graphSymbol_steinberg (k : Type u) [Field k] [CharZero k] (a b : kˣ)
    (hab : (b : k) = 1 - (a : k)) : graphSymbol k 2 ![a, b] = 0 :=
  graphSymbol_eq_zero_of_universal_annihilator 12 (by decide)
    universalSteinbergAnnihilator_twelve k a b hab

end AlgebraicGeometry.MotivicCohomology.DiagonalSteinbergBound
