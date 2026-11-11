/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.TensorProduct.ScalarExtension.LargePrime
import Colib.RingTheory.TranscendenceDegree.FiniteScalarExtension

open scoped TensorProduct

universe u v

example (e N : ℕ) (he : e ≠ 0) :
    ∃ n m : ℕ, n.Prime ∧ m.Prime ∧ N < n ∧ N < m ∧
      n ≠ m ∧ e.Coprime n ∧ e.Coprime m ∧ n.Coprime m :=
  Nat.exists_two_large_prime_degrees_coprime e N he

example (k : Type u) [Field k] (K L : Type v) [Field K] [Field L]
    [Algebra k K] [Algebra k L]
    (h : (Module.finrank k K).Coprime (Module.finrank k L)) :
    IsField (K ⊗[k] L) :=
  Algebra.TensorProduct.isField_of_coprime_finrank k K L h

example (k R L : Type u) [Field k] [CommRing R] [Field L]
    [Algebra k R] [Algebra k L] (x : PrimeSpectrum R)
    (h : (Module.finrank k x.asIdeal.ResidueField).Coprime (Module.finrank k L)) :
    ∃! y : PrimeSpectrum (R ⊗[k] L),
      PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x :=
  Algebra.TensorProduct.existsUnique_prime_over_of_coprime_residueDegree k R L x h

example (k R L : Type u) [Field k] [CommRing R] [IsDomain R] [Field L]
    [Algebra k R] [Algebra.Smooth k R] [Algebra k L]
    [Module.Finite k L] [Algebra.IsSeparable k L]
    (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    (h : (Module.finrank k x.asIdeal.ResidueField).Coprime (Module.finrank k L)) :
    IsDomain (R ⊗[k] L) ∧
      ∃! y : PrimeSpectrum (R ⊗[k] L),
        PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x :=
  Algebra.TensorProduct.isDomain_and_unique_prime_over_of_coprime_closedPoint k R L x h

example (k R : Type u) [Field k] [Finite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    {σ : Type u} [Finite σ] (q : MvPolynomial σ k) (hq : q ≠ 0) (N : ℕ) :
    ∃ n m : ℕ, n.Prime ∧ m.Prime ∧ N < n ∧ N < m ∧ n ≠ m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k p r)
        Module.finrank k L = r ∧ IsDomain (R ⊗[k] L) ∧
          (∃! y : PrimeSpectrum (R ⊗[k] L),
            PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x) ∧
          ∃ c : σ → L, MvPolynomial.eval₂ (algebraMap k L) c q ≠ 0 :=
  Algebra.TensorProduct.exists_two_large_prime_scalar_extensions k R p x q hq N

attribute [local instance] Algebra.TensorProduct.rightAlgebra

example (k R L : Type u) [Field k] [CommRing R] [Nontrivial R] [Field L]
    [Algebra k R] [Algebra k L] [Module.Finite k L] [IsDomain (R ⊗[k] L)] :
    Algebra.trdeg L (R ⊗[k] L) = Algebra.trdeg k R :=
  Algebra.TensorProduct.trdeg_right_eq_of_finite k R L
