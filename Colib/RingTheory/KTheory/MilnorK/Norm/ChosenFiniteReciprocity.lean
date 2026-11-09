/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenComparison
public import Colib.RingTheory.KTheory.MilnorK.Norm.FiniteReciprocity

/-!
# Finite reciprocity for the original chosen Milnor norm

In characteristic zero, the original chosen norm on each actual polynomial
quotient agrees with the original simple norm. Applying this comparison term by
term gives finite reciprocity for the chosen norms, with infinity coefficient
`+1` and no extra degree weights.

The quotient fields are the native `AdjoinRoot` fields of the actual monic
irreducible polynomials. Their finite-dimensional instances are constructed
from the native power bases in the statements, not supplied as assumptions.
The finite family index has an independent universe. No residue map or
polynomial-point carrier is introduced.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

variable {k : Type u} [Field k] [CharZero k] {ι : Type v}

/-- Reciprocity for prescribed, possibly nonhomogeneous classes in the actual
quotient fields. Extra points with zero residue are permitted in the family. -/
theorem sum_milnorKNormRing_eq_neg_infinityResidueRing_of_residues
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
      -infinityResidueRing k y := by
  intro hFinite
  calc
    (∑ i ∈ s, milnorKNormRing k (AdjoinRoot (poly (ψ i))) (α i)) =
        ∑ i ∈ s, simpleMilnorNorm (ψ i) (α i) :=
      Finset.sum_congr rfl (fun i _ => milnorKNormRing_eq_simpleMilnorNorm (ψ i) (α i))
    _ = -infinityResidueRing k y :=
      sum_simpleMilnorNorm_eq_neg_infinityResidueRing_of_residues
        s d ψ hinj α y hresidue hsupport

/-- Reciprocity on the literal sigma of monic irreducible polynomials, using
original chosen norms. Distinctness requires no separate hypothesis. -/
theorem sum_milnorKNormRing_residue_add_infinity_eq_zero
    (x : MilnorKRing (RatFunc k))
    (S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree k d))
    (hS : ∀ p ∉ S, monicIrreducibleResidue p.2 x = 0) :
    let _ : ∀ p : Σ d : ℕ, MonicIrreducibleOfDegree k d,
        FiniteDimensional k (AdjoinRoot (poly p.2)) :=
      fun p => (AdjoinRoot.powerBasis' (monic p.2)).finite
    (∑ p ∈ S, milnorKNormRing k (AdjoinRoot (poly p.2))
      (monicIrreducibleResidue p.2 x)) + infinityResidueRing k x = 0 := by
  intro hFinite
  have hsum :
      (∑ p ∈ S, milnorKNormRing k (AdjoinRoot (poly p.2))
        (monicIrreducibleResidue p.2 x)) =
        ∑ p ∈ S, simpleMilnorNorm p.2 (monicIrreducibleResidue p.2 x) :=
    Finset.sum_congr rfl (fun p _ =>
      milnorKNormRing_eq_simpleMilnorNorm p.2 (monicIrreducibleResidue p.2 x))
  rw [hsum]
  exact sum_simpleMilnorNorm_residue_add_infinity_eq_zero x S hS

/-- Every whole-ring class has finite affine support satisfying reciprocity
for the original chosen norms. No residue-support witness is an input. -/
theorem exists_finset_sum_milnorKNormRing_residue_add_infinity_eq_zero
    (x : MilnorKRing (RatFunc k)) :
    let _ : ∀ p : Σ d : ℕ, MonicIrreducibleOfDegree k d,
        FiniteDimensional k (AdjoinRoot (poly p.2)) :=
      fun p => (AdjoinRoot.powerBasis' (monic p.2)).finite
    ∃ S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree k d),
      (∀ p ∉ S, monicIrreducibleResidue p.2 x = 0) ∧
      (∑ p ∈ S, milnorKNormRing k (AdjoinRoot (poly p.2))
        (monicIrreducibleResidue p.2 x)) + infinityResidueRing k x = 0 := by
  intro hFinite
  obtain ⟨S, hS, _⟩ := exists_finset_sum_simpleMilnorNorm_residue_add_infinity_eq_zero x
  exact ⟨S, hS, sum_milnorKNormRing_residue_add_infinity_eq_zero x S hS⟩

end Stacks.Chow

end
