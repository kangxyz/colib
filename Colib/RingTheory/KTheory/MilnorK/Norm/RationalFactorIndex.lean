/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.CoefficientFactorSupport
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalConstant
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Complete native factor indices under rational constant extension

Every monic irreducible factor of a constant polynomial over `RatFunc k` is the
existing `ratFunc` image of a unique native monic irreducible factor over `k`.
The proof maps the full normalized-factor product, finds a factor by primality,
and upgrades associatedness to equality using monicity. Thus completeness is
proved, rather than imposed as a coverage hypothesis.

The resulting equivalence acts on the literal divisibility subtypes of the
existing sigma of `MonicIrreducibleOfDegree`. Polynomial formulas, degree,
multiplicity, exact finite-set images, and finite sums retain this same map.
There are no characteristic, separability, normality, or prime-degree assumptions.
No new point, branch, root field, residue, or norm model is introduced. This is
factor-index glue for the rational finite-place formula, not that norm formula
or a norm tower law.
-/

@[expose] public noncomputable section

open Polynomial UniqueFactorizationMonoid
open scoped BigOperators

namespace Stacks.Chow.MonicIrreducibleOfDegree

variable {k : Type*} [Field k]

/-- The existing rationalized native point has exactly the mapped polynomial. -/
@[simp]
theorem poly_ratFunc {d : ℕ} (p : MonicIrreducibleOfDegree k d) :
    poly p.ratFunc = (poly p).map (RatFunc.C : k →+* RatFunc k) :=
  rfl

/-- Divisibility between constant polynomials is both preserved and reflected. -/
theorem ratFunc_dvd_map_iff {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (f : k[X]) :
    poly p.ratFunc ∣ f.map (RatFunc.C : k →+* RatFunc k) ↔ poly p ∣ f :=
  Polynomial.map_dvd_map' (RatFunc.C : k →+* RatFunc k)

/-- The actual factor multiplicity is unchanged by rational constant extension. -/
theorem multiplicity_ratFunc {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (f : k[X]) :
    multiplicity (poly p.ratFunc) (f.map (RatFunc.C : k →+* RatFunc k)) =
      multiplicity (poly p) f := by
  apply multiplicity_eq_of_emultiplicity_eq
  apply emultiplicity_eq_emultiplicity_iff.mpr
  intro n
  change ((poly p).map (RatFunc.C : k →+* RatFunc k)) ^ n ∣ f.map RatFunc.C ↔ _
  rw [← Polynomial.map_pow]
  exact Polynomial.map_dvd_map' (RatFunc.C : k →+* RatFunc k)

/-- The literal rationalization map on the existing degree-indexed points is injective. -/
theorem sigma_ratFunc_injective :
    Function.Injective (fun p : Σ d : ℕ, MonicIrreducibleOfDegree k d =>
      (⟨p.1, p.2.ratFunc⟩ : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d)) := by
  intro p q h
  apply sigma_poly_injective
  apply Polynomial.map_injective (RatFunc.C : k →+* RatFunc k)
    (RatFunc.C : k →+* RatFunc k).injective
  exact congrArg (fun r : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d =>
    poly r.2) h

/-- Every rational factor of a monic constant polynomial comes from an actual
original factor. The complete normalized-factor product proves surjectivity. -/
theorem exists_ratFunc_of_dvd_map (f : k[X]) (hf : f.Monic)
    (q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d)
    (hq : poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)) :
    ∃ p : Σ d : ℕ, MonicIrreducibleOfDegree k d,
      poly p.2 ∣ f ∧
        (⟨p.1, p.2.ratFunc⟩ : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d) = q := by
  classical
  have hprod : (normalizedFactors f).prod = f := by
    simpa only [hf.leadingCoeff, Polynomial.C_1, one_mul] using
      Polynomial.leadingCoeff_mul_prod_normalizedFactors f
  have hqprod : poly q.2 ∣
      ((normalizedFactors f).map (Polynomial.map (RatFunc.C : k →+* RatFunc k))).prod := by
    rw [← Polynomial.map_multiset_prod, hprod]
    exact hq
  obtain ⟨g, hg, hqg⟩ := (irreducible q.2).prime.exists_mem_multiset_map_dvd hqprod
  obtain ⟨hgi, hgm, hgf⟩ := (Polynomial.mem_normalizedFactors_iff hf.ne_zero).mp hg
  have hpoly : poly q.2 = g.map (RatFunc.C : k →+* RatFunc k) :=
    Polynomial.eq_of_monic_of_associated (monic q.2) (hgm.map _)
      ((irreducible q.2).associated_of_dvd (hgm.irreducible_map_ratFunc_C hgi) hqg)
  refine ⟨⟨g.natDegree, ⟨g, hgm, hgi, rfl⟩⟩, hgf, ?_⟩
  apply sigma_poly_injective
  exact hpoly.symm

/-- Rationalization gives a bijection of the complete literal native factor subtypes. -/
def ratFuncFactorIndexEquiv (f : k[X]) (hf : f.Monic) :
    {p : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly p.2 ∣ f} ≃
      {q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d //
        poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)} :=
  Equiv.ofBijective
    (fun p => ⟨⟨p.1.1, p.1.2.ratFunc⟩, Polynomial.map_dvd RatFunc.C p.2⟩)
    ⟨fun p q h => Subtype.ext (sigma_ratFunc_injective (congrArg Subtype.val h)),
      fun q => by
        obtain ⟨p, hpf, hp⟩ := exists_ratFunc_of_dvd_map f hf q.1 q.2
        exact ⟨⟨p, hpf⟩, Subtype.ext hp⟩⟩

/-- The forward equivalence uses the existing point, not a separately selected factor. -/
theorem ratFuncFactorIndexEquiv_val (f : k[X]) (hf : f.Monic)
    (p : {p : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly p.2 ∣ f}) :
    (ratFuncFactorIndexEquiv f hf p).1 = ⟨p.1.1, p.1.2.ratFunc⟩ :=
  rfl

/-- The forward equivalence preserves the original degree index. -/
@[simp]
theorem ratFuncFactorIndexEquiv_degree (f : k[X]) (hf : f.Monic)
    (p : {p : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly p.2 ∣ f}) :
    (ratFuncFactorIndexEquiv f hf p).1.1 = p.1.1 :=
  rfl

/-- The forward equivalence retains the literal coefficient map. -/
@[simp]
theorem ratFuncFactorIndexEquiv_poly (f : k[X]) (hf : f.Monic)
    (p : {p : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly p.2 ∣ f}) :
    poly (ratFuncFactorIndexEquiv f hf p).1.2 =
      (poly p.1.2).map (RatFunc.C : k →+* RatFunc k) :=
  rfl

/-- The inverse equivalence recovers the degree of every rational factor. -/
@[simp]
theorem ratFuncFactorIndexEquiv_symm_degree (f : k[X]) (hf : f.Monic)
    (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d //
      poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)}) :
    ((ratFuncFactorIndexEquiv f hf).symm q).1.1 = q.1.1 :=
  congrArg (fun r : {r : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d //
    poly r.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)} => r.1.1)
      ((ratFuncFactorIndexEquiv f hf).apply_symm_apply q)

/-- Every rational factor is literally the map of its inverse image polynomial. -/
theorem ratFuncFactorIndexEquiv_symm_poly (f : k[X]) (hf : f.Monic)
    (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d //
      poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)}) :
    (poly ((ratFuncFactorIndexEquiv f hf).symm q).1.2).map RatFunc.C = poly q.1.2 :=
  congrArg (fun r : {r : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d //
    poly r.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)} => poly r.1.2)
      ((ratFuncFactorIndexEquiv f hf).apply_symm_apply q)

local instance rationalFactorIndexDecidableEq (K : Type*) [Field K] :
    DecidableEq (Σ d : ℕ, MonicIrreducibleOfDegree K d) :=
  Classical.decEq _

/-- The image of any exact original factor finset is the complete rational factor finset. -/
theorem mem_image_ratFunc_iff_dvd_map (f : k[X]) (hf : f.Monic)
    (S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree k d))
    (hS : ∀ p, p ∈ S ↔ poly p.2 ∣ f)
    (q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d) :
    q ∈ S.image (fun p =>
      (⟨p.1, p.2.ratFunc⟩ : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d)) ↔
      poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k) := by
  constructor
  · intro hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact Polynomial.map_dvd RatFunc.C ((hS p).mp hp)
  · intro hq
    obtain ⟨p, hpf, hp⟩ := exists_ratFunc_of_dvd_map f hf q hq
    exact Finset.mem_image.mpr ⟨p, (hS p).mpr hpf, hp⟩

/-- Both exact finite factor sets exist, with the rational one the actual image
of the original one. No factor-coverage assumption is an input. -/
theorem exists_finset_image_ratFunc (f : k[X]) (hf : f.Monic) :
    ∃ S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree k d),
      (∀ p, p ∈ S ↔ poly p.2 ∣ f) ∧
      ∀ q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d,
        q ∈ S.image (fun p =>
          (⟨p.1, p.2.ratFunc⟩ : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d)) ↔
          poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k) := by
  obtain ⟨S, hS⟩ := exists_finset_mem_iff_dvd_map (RingHom.id k) f hf.ne_zero
  have hS' : ∀ p, p ∈ S ↔ poly p.2 ∣ f := by
    simpa only [Polynomial.map_id] using hS
  exact ⟨S, hS', mem_image_ratFunc_iff_dvd_map f hf S hS'⟩

/-- Both literal factor subtypes are finite. No enumeration is required to establish this. -/
theorem finite_ratFuncFactorIndices (f : k[X]) (hf : f.Monic) :
    Finite {p : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly p.2 ∣ f} ∧
      Finite {q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d //
        poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)} := by
  obtain ⟨S, hS, _⟩ := exists_finset_image_ratFunc f hf
  let F : {p : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly p.2 ∣ f} → S :=
    fun p => ⟨p.1, (hS p.1).mpr p.2⟩
  let rationalFactorIndexSourceFinite :
      Finite {p : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly p.2 ∣ f} :=
    Finite.of_injective F (fun p q h => Subtype.ext (congrArg (fun t : S => t.val) h))
  exact ⟨inferInstance, Finite.of_equiv _ (ratFuncFactorIndexEquiv f hf)⟩

/-- Reindex a sum whose summand depends on the literal divisibility subtype.
The two finite enumerations exist by `finite_ratFuncFactorIndices`. -/
theorem sum_ratFuncFactorIndexEquiv {M : Type*} [AddCommMonoid M]
    (f : k[X]) (hf : f.Monic)
    [Fintype {p : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly p.2 ∣ f}]
    [Fintype {q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d //
      poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)}]
    (F : {q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d //
      poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)} → M) :
    ∑ q, F q = ∑ p, F (ratFuncFactorIndexEquiv f hf p) :=
  ((ratFuncFactorIndexEquiv f hf).sum_comp F).symm

/-- Finite sums over an actual image factor set reindex by the same native points. -/
theorem sum_image_ratFunc {M : Type*} [AddCommMonoid M]
    (S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree k d))
    (F : (Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d) → M) :
    ∑ q ∈ S.image (fun p =>
      (⟨p.1, p.2.ratFunc⟩ : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d)), F q =
      ∑ p ∈ S, F ⟨p.1, p.2.ratFunc⟩ :=
  Finset.sum_image sigma_ratFunc_injective.injOn

/-- The same finite sum reindexing retains every actual factor multiplicity. -/
theorem sum_multiplicity_image_ratFunc {M : Type*} [AddCommGroup M]
    (f : k[X]) (S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree k d))
    (F : (Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d) → M) :
    ∑ q ∈ S.image (fun p =>
      (⟨p.1, p.2.ratFunc⟩ : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d)),
        (multiplicity (poly q.2) (f.map RatFunc.C) : ℤ) • F q =
      ∑ p ∈ S, (multiplicity (poly p.2) f : ℤ) • F ⟨p.1, p.2.ratFunc⟩ := by
  rw [sum_image_ratFunc]
  apply Finset.sum_congr rfl
  intro p _
  rw [multiplicity_ratFunc]

end Stacks.Chow.MonicIrreducibleOfDegree
