/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenFiniteReciprocity

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u v

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

variable {k : Type u} [Field k] [CharZero k] {ι : Type v}

example
    (s : Finset ι) (d : ι → ℕ) (ψ : ∀ i, MonicIrreducibleOfDegree k (d i))
    (hinj : Set.InjOn (fun i => poly (ψ i)) (s : Set ι))
    (α : ∀ i, MilnorKRing (AdjoinRoot (poly (ψ i))))
    (y : MilnorKRing (RatFunc k))
    (hresidue : ∀ i ∈ s, monicIrreducibleResidue (ψ i) y = α i)
    (hsupport : ∀ (e : ℕ) (χ : MonicIrreducibleOfDegree k e),
      (∀ i ∈ s, poly χ ≠ poly (ψ i)) → monicIrreducibleResidue χ y = 0) :
    let _ : ∀ i, FiniteDimensional k (AdjoinRoot (poly (ψ i))) :=
      fun i => (AdjoinRoot.powerBasis' (monic (ψ i))).finite
    (∑ i ∈ s, milnorKNormRing k (AdjoinRoot (poly (ψ i))) (α i)) =
      -infinityResidueRing k y :=
  sum_milnorKNormRing_eq_neg_infinityResidueRing_of_residues s d ψ hinj α y hresidue hsupport

example
    (x : MilnorKRing (RatFunc k))
    (S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree k d))
    (hS : ∀ p ∉ S, monicIrreducibleResidue p.2 x = 0) :
    let _ : ∀ p : Σ d : ℕ, MonicIrreducibleOfDegree k d,
        FiniteDimensional k (AdjoinRoot (poly p.2)) :=
      fun p => (AdjoinRoot.powerBasis' (monic p.2)).finite
    (∑ p ∈ S, milnorKNormRing k (AdjoinRoot (poly p.2))
      (monicIrreducibleResidue p.2 x)) + infinityResidueRing k x = 0 :=
  sum_milnorKNormRing_residue_add_infinity_eq_zero x S hS

example
    (x : MilnorKRing (RatFunc k)) :
    let _ : ∀ p : Σ d : ℕ, MonicIrreducibleOfDegree k d,
        FiniteDimensional k (AdjoinRoot (poly p.2)) :=
      fun p => (AdjoinRoot.powerBasis' (monic p.2)).finite
    ∃ S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree k d),
      (∀ p ∉ S, monicIrreducibleResidue p.2 x = 0) ∧
      (∑ p ∈ S, milnorKNormRing k (AdjoinRoot (poly p.2))
        (monicIrreducibleResidue p.2 x)) + infinityResidueRing k x = 0 :=
  exists_finset_sum_milnorKNormRing_residue_add_infinity_eq_zero x

-- The empty support keeps the actual infinity term and requires no norm witness.
example (x : MilnorKRing (RatFunc k))
    (hx : ∀ (d : ℕ) (p : MonicIrreducibleOfDegree k d),
      monicIrreducibleResidue p x = 0) :
    let _ : ∀ p : Σ d : ℕ, MonicIrreducibleOfDegree k d,
        FiniteDimensional k (AdjoinRoot (poly p.2)) :=
      fun p => (AdjoinRoot.powerBasis' (monic p.2)).finite
    (∑ p ∈ (∅ : Finset (Σ d : ℕ, MonicIrreducibleOfDegree k d)),
      milnorKNormRing k (AdjoinRoot (poly p.2)) (monicIrreducibleResidue p.2 x)) +
        infinityResidueRing k x = 0 :=
  sum_milnorKNormRing_residue_add_infinity_eq_zero x ∅ (fun p _ => hx p.1 p.2)

-- The singleton family recovers the original single-residue norm with its sign.
example {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (x : MilnorKRing (AdjoinRoot (poly p))) (y : MilnorKRing (RatFunc k))
    (hy : IsSingleResidueLift p x y) :
    let _ : FiniteDimensional k (AdjoinRoot (poly p)) :=
      (AdjoinRoot.powerBasis' (monic p)).finite
    milnorKNormRing k (AdjoinRoot (poly p)) x = -infinityResidueRing k y := by
  intro hFinite
  have h := sum_milnorKNormRing_eq_neg_infinityResidueRing_of_residues
    ({()} : Finset Unit) (fun _ => d) (fun _ => p)
    (fun a _ b _ _ => Subsingleton.elim a b) (fun _ => x) y
    (fun _ _ => hy.1) (fun e q hq => hy.2 e q (hq () (Finset.mem_singleton_self ())))
  simpa only [Finset.sum_singleton] using h

end
