/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Finiteness over the coefficient ring of a Laurent algebra

The two Laurent coordinates generate the image of the Laurent algebra.
Over a field, a nonzero relation in the Laurent kernel makes both coordinates
algebraic, so a finite Laurent algebra is finite over the field.
-/

@[expose] public noncomputable section

open scoped Polynomial

universe u v

namespace LaurentPolynomial

section Integral

variable {R : Type u} [CommRing R] {D : Type v} [CommRing D] [Algebra R D]

/-- A finite Laurent algebra is finite over the coefficient ring when both
forward and inverse Laurent coordinates are integral over that ring. -/
theorem moduleFinite_of_integral_T_and_T_neg [Algebra (LaurentPolynomial R) D]
    [IsScalarTower R (LaurentPolynomial R) D] [Module.Finite (LaurentPolynomial R) D]
    (hpos : IsIntegral R (algebraMap (LaurentPolynomial R) D (T 1)))
    (hneg : IsIntegral R (algebraMap (LaurentPolynomial R) D (T (-1)))) : Module.Finite R D := by
  let f := IsScalarTower.toAlgHom R (LaurentPolynomial R) D
  let S := Algebra.adjoin R {f (T 1), f (T (-1))}
  have h₁ : f (T 1) ∈ S := Algebra.subset_adjoin (Set.mem_insert _ _)
  have h₂ : f (T (-1)) ∈ S :=
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hT (j : ℤ) : f (T j) ∈ S := by
    obtain ⟨i, rfl | rfl⟩ := Int.eq_nat_or_neg j
    · rw [show (T (i : ℤ) : LaurentPolynomial R) = T 1 ^ i by simp, map_pow]
      exact S.pow_mem h₁ i
    · rw [show (T (-(i : ℤ)) : LaurentPolynomial R) = T (-1) ^ i by simp, map_pow]
      exact S.pow_mem h₂ i
  have hmem (p : LaurentPolynomial R) : f p ∈ S := by
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
    | C_mul_T j a =>
      rw [map_mul, LaurentPolynomial.C_eq_algebraMap, AlgHom.commutes]
      exact S.mul_mem (S.algebraMap_mem a) (hT j)
  let g := f.codRestrict S hmem
  let : Algebra (LaurentPolynomial R) S := g.toRingHom.toAlgebra
  let : IsScalarTower (LaurentPolynomial R) S D :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.Finite S D := Module.Finite.of_restrictScalars_finite (LaurentPolynomial R) S D
  let : Module.Finite R S := Algebra.finite_adjoin_of_finite_of_isIntegral
    ((Set.finite_singleton _).insert _) (by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact hpos
      · rw [Set.mem_singleton_iff.mp hz]
        exact hneg)
  exact Module.Finite.trans S D

end Integral

/-- A finite algebra over a Laurent polynomial ring over a field is finite over
that field if the Laurent structure map has a nonzero kernel. -/
theorem finite_comp_C_of_not_injective {K : Type u} [Field K] {B : Type v} [CommRing B]
    (φ : LaurentPolynomial K →+* B) (hφ : φ.Finite) (h : ¬ Function.Injective φ) :
    (φ.comp LaurentPolynomial.C).Finite := by
  let L := LaurentPolynomial K
  rw [RingHom.injective_iff_ker_eq_bot] at h
  obtain ⟨r, hr, hrne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨d, p, hp⟩ := r.exists_T_pow
  have hr_eq : r = p.toLaurent * T (-(d : ℤ)) := by
    rw [hp, mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one]
  have hp0 : p ≠ 0 := by
    intro he
    exact hrne (by simp [hr_eq, he])
  have hpφ : φ p.toLaurent = 0 := by
    rw [hp, map_mul, RingHom.mem_ker.mp hr, zero_mul]
  let : Algebra L B := φ.toAlgebra
  let : Algebra K B := (φ.comp LaurentPolynomial.C).toAlgebra
  let : IsScalarTower K L B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.Finite L B := hφ
  let v := algebraMap L B (T 1)
  let w := algebraMap L B (T (-1))
  have hvw : v * w = 1 := by
    dsimp only [v, w]
    rw [← map_mul, ← T_add, add_neg_cancel, T_zero, map_one]
  have hv : IsAlgebraic K v := ⟨p, hp0, by
    have he : Polynomial.aeval (T 1 : L) = Polynomial.toLaurentAlg := by
      apply Polynomial.algHom_ext
      simp only [Polynomial.aeval_X, Polynomial.coe_toLaurentAlg, Polynomial.toLaurent_X]
    change Polynomial.aeval (IsScalarTower.toAlgHom K L B (T 1)) p = 0
    rw [Polynomial.aeval_algHom_apply, he, Polynomial.coe_toLaurentAlg]
    exact hpφ⟩
  let : Invertible v := invertibleOfRightInverse v w hvw
  have hw : IsAlgebraic K w := invOf_eq_right_inv hvw ▸ hv.invOf
  exact moduleFinite_of_integral_T_and_T_neg hv.isIntegral hw.isIntegral

end LaurentPolynomial
