/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.RingTheory.KTheory.MilnorK.PolynomialFiltrationExactness
public import Colib.RingTheory.KTheory.MilnorK.RationalFunctionExactness

/-!
# Bounded residue lifting in native rational-function Milnor K-theory

The original total residue characterizes membership in the native polynomial
filtration by residue support at points of bounded degree. Consequently every
such vector has a lift in that same filtration stage. Prescribing the original
constant retraction makes the lift unique, without enlarging its degree bound.

This completes the bounded-support part of the rational exactness argument from
`Aglib.KTheory.MilnorK.RationalExactness` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f` on the native objects. The native bound
is weak: polynomial degrees at most `d`. The source uses strict bounds; its
positive bound `d + 1` therefore corresponds to this bound `d`. No equality of
the source's separate filtration model or specialization map with the native
ones is asserted. In particular the native stage zero contains constants.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

variable (k : Type u) [Field k]

attribute [local instance] Ideal.Quotient.field

/-- The original total residue detects the native polynomial filtration exactly
by the degrees of its support. Its kernel of constants is retained. -/
theorem mem_milnorKPolyFiltration_iff_totalResidue_eq_zero_above (n d : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    (x : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k d ↔
      ∀ p : MonicIrreduciblePoint k, d < p.1 → milnorKTotalResidue k n x p = 0 := by
  rw [mem_milnorKPolyFiltration_iff_residue_eq_zero_above]
  constructor
  · intro hx p hp
    apply Subtype.ext
    change (milnorKTotalResidue k n x p :
      MilnorKRing (Polynomial k ⧸ Ideal.span {poly p.2})) = 0
    rw [coe_milnorKTotalResidue_apply]
    exact hx p.1 p.2 hp
  · intro hx e ψ hde
    have hzero : (milnorKTotalResidue k n x ⟨e, ψ⟩ :
        MilnorKRing (Polynomial k ⧸ Ideal.span {poly ψ})) = 0 :=
      congrArg Subtype.val (hx ⟨e, ψ⟩ hde)
    rw [coe_milnorKTotalResidue_apply] at hzero
    exact hzero

/-- The kernel of the actual total residue is the polynomial stage zero. -/
theorem milnorKTotalResidue_eq_zero_iff_mem_milnorKPolyFiltration_zero (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    milnorKTotalResidue k n x = 0 ↔
      (x : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k 0 := by
  rw [mem_milnorKPolyFiltration_iff_totalResidue_eq_zero_above]
  constructor
  · intro hx p _
    rw [hx]
    rfl
  · intro hx
    apply DFinsupp.ext
    rintro ⟨d, ψ⟩
    cases d with
    | zero => exact (MonicIrreducibleOfDegree.isEmpty_zero.false ψ).elim
    | succ d => exact hx ⟨d + 1, ψ⟩ (Nat.zero_lt_succ d)

/-- Every residue vector supported in degrees at most `d` has a lift in the
same native polynomial stage. No larger polynomial degree bound is used. -/
theorem exists_mem_milnorKPolyFiltration_totalResidue_eq (n d : ℕ)
    (z : DirectSum (MonicIrreduciblePoint k)
      (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) n))
    (hz : ∀ p : MonicIrreduciblePoint k, d < p.1 → z p = 0) :
    ∃ x : MilnorKTheory (RatFunc k) (n + 1),
      (x : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k d ∧
        milnorKTotalResidue k n x = z := by
  obtain ⟨x, hx⟩ := milnorKTotalResidue_surjective n z
  refine ⟨x, ?_, hx⟩
  apply (mem_milnorKPolyFiltration_iff_totalResidue_eq_zero_above k n d x).mpr
  simpa only [hx] using hz

/-- In the original splitting, polynomial degree depends only on residue support,
not on the chosen constant component. -/
theorem milnorKRationalDecomposition_symm_mem_milnorKPolyFiltration_iff (n d : ℕ)
    (a : MilnorKTheory k (n + 1))
    (z : DirectSum (MonicIrreduciblePoint k)
      (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) n)) :
    ((milnorKRationalDecomposition k n).symm (a, z) : MilnorKRing (RatFunc k)) ∈
      milnorKPolyFiltration k d ↔
        ∀ p : MonicIrreduciblePoint k, d < p.1 → z p = 0 := by
  rw [mem_milnorKPolyFiltration_iff_totalResidue_eq_zero_above,
    milnorKTotalResidue_milnorKRationalDecomposition_symm]

/-- Prescribing both the original constant retraction and a bounded residue
vector gives a unique lift at the same bound, including residue degree zero. -/
theorem existsUnique_mem_milnorKPolyFiltration_lift (n d : ℕ)
    (a : MilnorKTheory k (n + 1))
    (z : DirectSum (MonicIrreduciblePoint k)
      (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) n))
    (hz : ∀ p : MonicIrreduciblePoint k, d < p.1 → z p = 0) :
    ∃! x : MilnorKTheory (RatFunc k) (n + 1),
      (x : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k d ∧
        constantRetraction (n + 1) x = a ∧ milnorKTotalResidue k n x = z := by
  refine ⟨(milnorKRationalDecomposition k n).symm (a, z), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (milnorKRationalDecomposition_symm_mem_milnorKPolyFiltration_iff k n d a z).mpr hz
  · exact constantRetraction_milnorKRationalDecomposition_symm k n a z
  · exact milnorKTotalResidue_milnorKRationalDecomposition_symm k n a z
  · intro x hx
    apply (milnorKRationalDecomposition k n).injective
    rw [LinearEquiv.apply_symm_apply, milnorKRationalDecomposition_apply, hx.2.1, hx.2.2]

end Stacks.Chow

attribute [colib_tag "COL-0345",
  colib_ref "Milnor1970" "Section 2, Theorem 2.3, p. 325, and proof conclusion, p. 327" "adaptation"
    "Split exact sequence; native retraction and bounded normalized uniqueness are retained"]
  Stacks.Chow.existsUnique_mem_milnorKPolyFiltration_lift
