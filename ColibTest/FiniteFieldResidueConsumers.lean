/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.TensorProduct.ScalarExtension.LargePrimeResidueUnits

open scoped TensorProduct

universe u v w

example {L : Type u} [Field L] {B : Type v} [CommRing B] [Algebra L B]
    [Module.Finite L B] (b : B) (hb : Algebra.norm L b ≠ 0) : IsUnit b :=
  Algebra.isUnit_of_norm_ne_zero b hb

example {L : Type u} [Field L] {B : Type v} [CommRing B] [Algebra L B]
    [Module.Finite L B] (b : B) (hb : Algebra.norm L b ≠ 0)
    {E : Type w} [Field E] (f : B →+* E) : f b ≠ 0 :=
  Algebra.map_ne_zero_of_norm_ne_zero b hb f

example (k : Type u) [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (K : Type v) [Field K] [Algebra k K] [Module.Finite k K]
    {σ : Type w} [Finite σ] (q : MvPolynomial σ K) (hq : q ≠ 0) :
    ∃ N : ℕ, ∀ (n : ℕ) [NeZero n], N < n →
      ∃ c : σ → FiniteField.Extension k p n,
        let : Algebra (MvPolynomial σ k) (FiniteField.Extension k p n) :=
          (MvPolynomial.eval₂Hom (algebraMap k (FiniteField.Extension k p n)) c).toAlgebra
        IsUnit (1 ⊗ₜ[MvPolynomial σ k] (MvPolynomial.residueCoefficientEquiv k K σ).symm q :
          FiniteField.Extension k p n ⊗[MvPolynomial σ k]
            (MvPolynomial σ k ⊗[k] K)) :=
  MvPolynomial.exists_isUnit_residuePolynomial_finiteExtension k p K q hq

example
    (k R : Type u) [Field k] [Finite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    {σ ι : Type u} [Finite σ] [Finite ι]
    (K : ι → Type u) [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    [∀ i, Module.Finite k (K i)]
    (q : MvPolynomial σ k) (hq : q ≠ 0)
    (f : (i : ι) → MvPolynomial σ (K i)) (hf : ∀ i, f i ≠ 0) (N : ℕ) :
    ∃ n m : ℕ, n.Prime ∧ m.Prime ∧ N < n ∧ N < m ∧ n ≠ m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k p r)
        Module.finrank k L = r ∧ IsDomain (R ⊗[k] L) ∧
          (∃! y : PrimeSpectrum (R ⊗[k] L),
            PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x) ∧
          ∃ c : σ → L, MvPolynomial.eval₂ (algebraMap k L) c q ≠ 0 ∧
            (let : Algebra (MvPolynomial σ k) L :=
              (MvPolynomial.eval₂Hom (algebraMap k L) c).toAlgebra
             ∀ i, IsUnit
              (1 ⊗ₜ[MvPolynomial σ k] (MvPolynomial.residueCoefficientEquiv k (K i) σ).symm
                (f i) : L ⊗[MvPolynomial σ k] (MvPolynomial σ k ⊗[k] K i))) :=
  Algebra.TensorProduct.exists_two_large_prime_scalar_extensions_with_residue_units
    k R p x K q hq f hf N
