module

import Colib.RingTheory.KTheory.MilnorK.RationalFunctionBoundedResidues

open Stacks.Chow MonicIrreducibleOfDegree

universe u

variable (k : Type u) [Field k]

attribute [local instance] Ideal.Quotient.field

-- The finite support coordinates are the original native total residue.
example (n d : ℕ) (x : MilnorKTheory (RatFunc k) (n + 1)) :
    (x : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k d ↔
      ∀ p : MonicIrreduciblePoint k, d < p.1 → milnorKTotalResidue k n x p = 0 :=
  mem_milnorKPolyFiltration_iff_totalResidue_eq_zero_above k n d x

-- Residue degree zero still gives a bounded degree-one lift with any constant component.
example (d : ℕ) (a : MilnorKTheory k 1)
    (z : DirectSum (MonicIrreduciblePoint k)
      (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) 0))
    (hz : ∀ p : MonicIrreduciblePoint k, d < p.1 → z p = 0) :
    ∃! x : MilnorKTheory (RatFunc k) 1,
      (x : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k d ∧
        constantRetraction 1 x = a ∧ milnorKTotalResidue k 0 x = z :=
  existsUnique_mem_milnorKPolyFiltration_lift k 0 d a z hz

-- The exact native stage-zero kernel includes constants and is not assumed trivial.
example (n : ℕ) (x : MilnorKTheory (RatFunc k) (n + 1)) :
    milnorKTotalResidue k n x = 0 ↔
      (x : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k 0 :=
  milnorKTotalResidue_eq_zero_iff_mem_milnorKPolyFiltration_zero k n x

-- Polynomial degree depends only on the residue coordinates of the original splitting.
example (n d : ℕ) (a : MilnorKTheory k (n + 1))
    (z : DirectSum (MonicIrreduciblePoint k)
      (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) n)) :
    ((milnorKRationalDecomposition k n).symm (a, z) : MilnorKRing (RatFunc k)) ∈
      milnorKPolyFiltration k d ↔
        ∀ p : MonicIrreduciblePoint k, d < p.1 → z p = 0 :=
  milnorKRationalDecomposition_symm_mem_milnorKPolyFiltration_iff k n d a z
