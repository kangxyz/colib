/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Bertini.QuadraticCoordinates
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.Data.Finset.Max

/-! # A valuation pole produces an actual quadratic infinity point

A maximal original monomial supplies the original ratio chart. Its inverse is
in the valuation maximal ideal. Reduction of that entire chart, including its
full infinity quotient, produces the forbidden field-valued common zero.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.MvPolynomial
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} [Fintype σ] (g : σ → R)

/-- All original monomials lie in a valuation ring containing the chosen
coordinates if those same coordinates have no common infinity zero. -/
theorem monomial_mem_valuationSubring_of_no_infinity
    (d : ℕ) (c : Fin d × Exponent σ → k)
    (h : ∀ j : Exponent σ, monomialFunction k R g j ≠ 0 →
      ∀ (K : Type u) [Field K] [Algebra k K] [Algebra (boundaryRing k R g j) K]
        [IsScalarTower k (boundaryRing k R g j) K],
        ¬ ProjectiveEvaluationIncidence.Vanishes k (boundaryRing k R g j) K
          (boundaryCoordinate k R g j) d c)
    (V : ValuationSubring (FractionRing R))
    (hk : ∀ a : k, algebraMap k (FractionRing R) a ∈ V)
    (hc : ∀ i : Fin d, algebraMap R (FractionRing R)
      (aeval g (parameterTuple k σ d c i).val) ∈ V) :
    ∀ e : Exponent σ, algebraMap R (FractionRing R) (monomialFunction k R g e) ∈ V := by
  classical
  let F := FractionRing R
  let m : Exponent σ → F := fun e => algebraMap R F (monomialFunction k R g e)
  by_contra! he
  obtain ⟨e, he⟩ := he
  obtain ⟨j, _, hjmax⟩ := Finset.exists_max_image Finset.univ (fun e => V.valuation (m e))
    ⟨constantIndex, Finset.mem_univ _⟩
  have hjV : m j ∉ V := by
    intro hjV
    exact he (V.mem_of_valuation_le_one _
      ((hjmax e (Finset.mem_univ _)).trans (V.valuation_le_one ⟨m j, hjV⟩)))
  have hjF : m j ≠ 0 := by
    intro hz
    apply hjV
    simpa only [hz] using V.zero_mem
  have hj : monomialFunction k R g j ≠ 0 := by
    intro hz
    apply hjF
    simp only [m, hz, map_zero]
  have hratio (e : Exponent σ) : ratio k R g j e ∈ V := by
    obtain ⟨v, hv⟩ := (V.valuation_le_iff (m e) (m j)).mp
      (hjmax e (Finset.mem_univ _))
    have heq : ratio k R g j e = (v : F) := (div_eq_iff hjF).mpr hv.symm
    rw [heq]
    exact v.property
  have hinv : (m j)⁻¹ ∈ V.nonunits := V.inv_mem_nonunits_iff.mpr (Or.inr hjV)
  let κ : k →+* V := (algebraMap k F).codRestrict V hk
  let : Algebra k V := κ.toAlgebra
  let : IsScalarTower k V F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let T : Subalgebra k F :=
    { __ := V.toSubring.toSubsemiring
      algebraMap_mem' := hk }
  have hchart : chart k R g j ≤ T := by
    rw [chart_eq_adjoin_ratios]
    exact Algebra.adjoin_le (by rintro _ ⟨e, rfl⟩; exact hratio e)
  let χ : chart k R g j →ₐ[k] V :=
    { __ := (chart k R g j).val.toRingHom.codRestrict V (fun a => hchart a.property)
      commutes' := fun _ => Subtype.ext rfl }
  let K := IsLocalRing.ResidueField V
  let qχ : chart k R g j →ₐ[k] K :=
    (Ideal.Quotient.mkₐ k (IsLocalRing.maximalIdeal V)).comp χ
  have hi : χ (infinityCoordinate k R g j) ∈ IsLocalRing.maximalIdeal V :=
    ValuationSubring.coe_mem_nonunits_iff.mp hinv
  have hker : Ideal.span {infinityCoordinate k R g j} ≤ RingHom.ker qχ.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ rfl
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hi
  let ψ : boundaryRing k R g j →ₐ[k] K :=
    Ideal.Quotient.liftₐ _ qχ (fun a ha => hker ha)
  let : Algebra (boundaryRing k R g j) K := ψ.toRingHom.toAlgebra
  let : IsScalarTower k (boundaryRing k R g j) K :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := boundaryRing k R g j) (A := K)
      (fun a => (ψ.commutes a).symm)
  apply h j hj (IsLocalRing.ResidueField V)
  intro i
  let r : Exponent σ → chart k R g j := fun e =>
    ⟨ratio k R g j e, Algebra.subset_adjoin (Or.inl ⟨e, rfl⟩)⟩
  let y : chart k R g j := ∑ e, algebraMap k (chart k R g j) (c (i, e)) * r e
  let v : V := ⟨algebraMap R F (aeval g (parameterTuple k σ d c i).val), hc i⟩
  have hy : χ y = v * χ (infinityCoordinate k R g j) := by
    apply Subtype.ext
    change (chart k R g j).val y =
      algebraMap R F (aeval g (parameterTuple k σ d c i).val) * (m j)⁻¹
    simp only [y, map_sum, map_mul, AlgHom.commutes]
    change (∑ e, algebraMap k F (c (i, e)) * ratio k R g j e) =
      algebraMap R F (aeval g (parameterTuple k σ d c i).val) * (m j)⁻¹
    rw [originalFunction_eq_sum_rows, map_sum]
    simp only [map_mul, ← IsScalarTower.algebraMap_apply k R F,
      Finset.sum_mul, ratio, div_eq_mul_inv, mul_assoc, m]
    rfl
  have hy0 : qχ y = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change χ y ∈ IsLocalRing.maximalIdeal V
    exact hy.symm ▸ (IsLocalRing.maximalIdeal V).mul_mem_left v hi
  have hcoord (e : Exponent σ) :
      ψ (boundaryCoordinate k R g j e) = qχ (r e) := rfl
  change ∑ e, algebraMap k K (c (i, e)) * ψ (boundaryCoordinate k R g j e) = 0
  simp_rw [hcoord]
  simpa only [y, map_sum, map_mul, AlgHom.commutes] using hy0

end QuadraticIncidence.InfinityChart
