module

import Colib.RingTheory.KTheory.MilnorK.RationalFunctionInfinity

open Stacks.Chow MonicIrreducibleOfDegree

universe u

variable (k : Type u) [Field k]

attribute [local instance] Ideal.Quotient.field

-- The infinity formula uses the literal native degree-zero residue vector.
open Classical in
example (a : MilnorKTheory k 1)
    (z : DirectSum (MonicIrreduciblePoint k)
      (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) 0)) :
    infinityResidueRing k ((milnorKRationalDecomposition k 0).symm (a, z)) =
      -(∑ p ∈ z.support, simpleMilnorNorm p.2 (z p)) :=
  infinityResidueRing_milnorKRationalDecomposition_symm k 0 a z

-- A constant component with an empty finite residue vector has zero infinity residue.
open Classical in
example (n : ℕ) (a : MilnorKTheory k (n + 1)) :
    infinityResidueRing k ((milnorKRationalDecomposition k n).symm (a, 0)) = 0 := by
  simp only [infinityResidueRing_milnorKRationalDecomposition_symm,
    DFinsupp.support_zero, Finset.sum_empty, neg_zero]

-- Prescribing the native constant component strengthens quotient uniqueness
-- to uniqueness of the actual bounded homogeneous lift.
open Classical in
example (n d : ℕ) (a : MilnorKTheory k (n + 1))
    (z : DirectSum (MonicIrreduciblePoint k)
      (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) n))
    (hz : ∀ p : MonicIrreduciblePoint k, d < p.1 → z p = 0)
    (β : MilnorKRing k)
    (hβ : (∑ p ∈ z.support, simpleMilnorNorm p.2 (z p)) + β = 0) :
    ∃! x : MilnorKTheory (RatFunc k) (n + 1),
      (x : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k d ∧
      constantRetraction (n + 1) x = a ∧ milnorKTotalResidue k n x = z ∧
      infinityResidueRing k x = β :=
  existsUnique_bounded_normalized_totalResidue_lift_with_infinity k n d a z hz β hβ
