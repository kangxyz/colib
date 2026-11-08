/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.RationalFunctionBoundedResidues
public import Colib.RingTheory.KTheory.MilnorK.Norm.FiniteReciprocity

/-!
# Infinity residue in the native rational Milnor decomposition

The infinity residue of the original rational-function decomposition is the
negative sum of the existing simple norms of its actual finite residue vector.
It depends only on that vector, not on the native constant component.

Consequently a bounded finite residue vector, a constant component and an
infinity value have a simultaneous lift exactly when the norm-sum obstruction
vanishes. When compatible, that normalized bounded lift is unique as an element
of the original homogeneous Milnor group.

Only the existing total residue, its actual finite support, simple norms and
infinity residue occur. No total-norm map or replacement residue coordinates
are introduced. The reciprocity input is the maintained native finite
reciprocity theorem, not an additional norm-independence assumption.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
open scoped Classical

variable (k : Type u) [Field k]

attribute [local instance] Ideal.Quotient.field

/-- Reciprocity on the exact support of the original total residue vector. -/
theorem sum_simpleMilnorNorm_totalResidue_add_infinity_eq_zero (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    (∑ p ∈ (milnorKTotalResidue k n x).support,
      simpleMilnorNorm p.2 (milnorKTotalResidue k n x p)) +
        infinityResidueRing k x = 0 := by
  have hsupport : ∀ p ∉ (milnorKTotalResidue k n x).support,
      monicIrreducibleResidue p.2 x = 0 := by
    intro p hp
    have hz : (milnorKTotalResidue k n x p :
        MilnorKRing (Polynomial k ⧸ Ideal.span {poly p.2})) = 0 :=
      congrArg Subtype.val (DFinsupp.notMem_support_iff.mp hp)
    rw [coe_milnorKTotalResidue_apply] at hz
    exact hz
  simpa only [coe_milnorKTotalResidue_apply] using
    sum_simpleMilnorNorm_residue_add_infinity_eq_zero
      (x : MilnorKRing (RatFunc k)) (milnorKTotalResidue k n x).support hsupport

/-- The infinity coordinate of the native splitting is fixed by its residue
vector and is independent of its prescribed constant component. -/
theorem infinityResidueRing_milnorKRationalDecomposition_symm (n : ℕ)
    (a : MilnorKTheory k (n + 1))
    (z : DirectSum (MonicIrreduciblePoint k)
      (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) n)) :
    infinityResidueRing k ((milnorKRationalDecomposition k n).symm (a, z)) =
      -(∑ p ∈ z.support, simpleMilnorNorm p.2 (z p)) := by
  have h := sum_simpleMilnorNorm_totalResidue_add_infinity_eq_zero k n
    ((milnorKRationalDecomposition k n).symm (a, z))
  rw [milnorKTotalResidue_milnorKRationalDecomposition_symm] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Prescribing infinity along with the original constant and finite residue
coordinates has exactly the native norm-sum obstruction, with the same bound. -/
theorem exists_bounded_normalized_totalResidue_lift_with_infinity_iff (n d : ℕ)
    (a : MilnorKTheory k (n + 1))
    (z : DirectSum (MonicIrreduciblePoint k)
      (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) n))
    (hz : ∀ p : MonicIrreduciblePoint k, d < p.1 → z p = 0)
    (β : MilnorKRing k) :
    (∃ x : MilnorKTheory (RatFunc k) (n + 1),
      (x : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k d ∧
      constantRetraction (n + 1) x = a ∧ milnorKTotalResidue k n x = z ∧
      infinityResidueRing k x = β) ↔
      (∑ p ∈ z.support, simpleMilnorNorm p.2 (z p)) + β = 0 := by
  constructor
  · rintro ⟨x, _, _, hx, hInfinity⟩
    have h := sum_simpleMilnorNorm_totalResidue_add_infinity_eq_zero k n x
    rwa [hx, hInfinity] at h
  · intro hβ
    refine ⟨(milnorKRationalDecomposition k n).symm (a, z), ?_, ?_, ?_, ?_⟩
    · exact (milnorKRationalDecomposition_symm_mem_milnorKPolyFiltration_iff
        k n d a z).mpr hz
    · exact constantRetraction_milnorKRationalDecomposition_symm k n a z
    · exact milnorKTotalResidue_milnorKRationalDecomposition_symm k n a z
    · rw [infinityResidueRing_milnorKRationalDecomposition_symm]
      exact (eq_neg_of_add_eq_zero_right hβ).symm

/-- Compatible constant, finite and infinity coordinates have a unique bounded
homogeneous lift, including degree-zero finite residue vectors. -/
theorem existsUnique_bounded_normalized_totalResidue_lift_with_infinity (n d : ℕ)
    (a : MilnorKTheory k (n + 1))
    (z : DirectSum (MonicIrreduciblePoint k)
      (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) n))
    (hz : ∀ p : MonicIrreduciblePoint k, d < p.1 → z p = 0)
    (β : MilnorKRing k)
    (hβ : (∑ p ∈ z.support, simpleMilnorNorm p.2 (z p)) + β = 0) :
    ∃! x : MilnorKTheory (RatFunc k) (n + 1),
      (x : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k d ∧
      constantRetraction (n + 1) x = a ∧ milnorKTotalResidue k n x = z ∧
      infinityResidueRing k x = β := by
  obtain ⟨x, hx⟩ :=
    (exists_bounded_normalized_totalResidue_lift_with_infinity_iff k n d a z hz β).mpr hβ
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply (milnorKRationalDecomposition k n).injective
  rw [milnorKRationalDecomposition_apply, milnorKRationalDecomposition_apply,
    hy.2.1, hx.2.1, hy.2.2.1, hx.2.2.1]

end Stacks.Chow
