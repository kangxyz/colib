module

import Colib.RingTheory.KTheory.MilnorK.SingleResidueFiltration

open Stacks.Chow MonicIrreducibleOfDegree

universe u

variable (k : Type u) [Field k]

attribute [local instance] Ideal.Quotient.field

-- The literal native homogeneous group and single-residue predicate are kept.
example (d n : ℕ) (φ : MonicIrreducibleOfDegree k d)
    (α : MilnorKTheory (Polynomial k ⧸ Ideal.span {poly φ}) n) :
    ∃ y ∈ milnorKGrading (RatFunc k) (n + 1),
      y ∈ milnorKPolyFiltration k d ∧ IsSingleResidueLift φ α y :=
  exists_isSingleResidueLift_mem_milnorKPolyFiltration φ α.2

-- Residue degree zero still has a bounded degree-one homogeneous lift.
example (d : ℕ) (φ : MonicIrreducibleOfDegree k d)
    (α : MilnorKTheory (Polynomial k ⧸ Ideal.span {poly φ}) 0) :
    ∃! q : milnorKPolyQuotient k 0,
      ∃ y ∈ milnorKGrading (RatFunc k) 1,
        y ∈ milnorKPolyFiltration k d ∧ IsSingleResidueLift φ α y ∧
          milnorKPolyQuotientMk k 0 y = q :=
  existsUnique_bounded_singleResidue_quotient_class φ α.2

-- Uniqueness modulo native F0 applies even to inhomogeneous lifts.
example (d : ℕ) (φ : MonicIrreducibleOfDegree k d)
    (α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ}))
    (y z : MilnorKRing (RatFunc k))
    (hy : IsSingleResidueLift φ α y) (hz : IsSingleResidueLift φ α z) :
    y - z ∈ milnorKPolyFiltration k 0 ∧
      milnorKPolyQuotientMk k 0 y = milnorKPolyQuotientMk k 0 z :=
  ⟨hy.sub_mem_milnorKPolyFiltration_zero hz, hy.milnorKPolyQuotientMk_zero_eq hz⟩
