/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.PolynomialFiltrationExactness
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.SimpleNorm

/-!
# Bounded single-residue lifting on the native polynomial filtration

A native single-residue lift at a monic irreducible polynomial of degree `d`
already lies in the native polynomial filtration stage `d`: all higher-degree
residues vanish, so the filtration criterion applies. Native homogeneous
single-residue surjectivity therefore gives a lift with this same bound.

Two lifts of the same residue differ in the polynomial stage zero. Consequently
the bounded homogeneous lift determines a unique class in the existing quotient
by that stage. This strengthens the intermediate kernel argument in Stacks'
`infinityResidueRing_eq_of_isSingleResidueLift`; it retains the quotient class
rather than only its residue at infinity.

Only the original filtration, original single-residue predicate, original
residue-field quotient and original additive quotient are used. No global total
residue map, alternate point indexing or replacement Milnor model is introduced.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

variable {k : Type u} [Field k]

attribute [local instance] Ideal.Quotient.field

/-- Every native single-residue lift lies in the polynomial stage indexed by
the degree of its one possible nonzero residue. -/
theorem IsSingleResidueLift.mem_milnorKPolyFiltration {d : ℕ}
    {φ : MonicIrreducibleOfDegree k d}
    {α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})}
    {y : MilnorKRing (RatFunc k)} (hy : IsSingleResidueLift φ α y) :
    y ∈ milnorKPolyFiltration k d := by
  apply mem_milnorKPolyFiltration_of_forall_monicIrreducibleResidue_eq_zero_above d
  intro e ψ hde
  apply hy.2 e ψ
  intro hp
  have hdeg := congrArg Polynomial.natDegree hp
  rw [natDegree_eq ψ, natDegree_eq φ] at hdeg
  exact (ne_of_lt hde) hdeg.symm

/-- The native homogeneous single-residue lift can be chosen in the polynomial
stage given by the residue polynomial's degree. Residue degree zero is included. -/
theorem exists_isSingleResidueLift_mem_milnorKPolyFiltration {d : ℕ}
    (φ : MonicIrreducibleOfDegree k d) {n : ℕ}
    {α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})}
    (hα : α ∈ milnorKGrading (Polynomial k ⧸ Ideal.span {poly φ}) n) :
    ∃ y ∈ milnorKGrading (RatFunc k) (n + 1),
      y ∈ milnorKPolyFiltration k d ∧ IsSingleResidueLift φ α y := by
  obtain ⟨y, hyn, hy⟩ := exists_isSingleResidueLift' φ hα
  exact ⟨y, hyn, hy.mem_milnorKPolyFiltration, hy⟩

/-- The difference of two native single-residue lifts of the same class lies
in the polynomial stage zero. No homogeneity assumption is needed. -/
theorem IsSingleResidueLift.sub_mem_milnorKPolyFiltration_zero {d : ℕ}
    {φ : MonicIrreducibleOfDegree k d}
    {α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})}
    {y z : MilnorKRing (RatFunc k)}
    (hy : IsSingleResidueLift φ α y) (hz : IsSingleResidueLift φ α z) :
    y - z ∈ milnorKPolyFiltration k 0 := by
  apply mem_milnorKPolyFiltration_zero_of_forall_monicIrreducibleResidue_eq_zero
  intro e ψ
  by_cases hp : poly ψ = poly φ
  · exact monicIrreducibleResidue_eq_zero_of_poly_eq hp.symm
      (by rw [map_sub, hy.1, hz.1, sub_self])
  · rw [map_sub, hy.2 _ ψ hp, hz.2 _ ψ hp, sub_self]

/-- The class of a native single-residue lift in the existing quotient by
polynomial stage zero is independent of the chosen lift. -/
theorem IsSingleResidueLift.milnorKPolyQuotientMk_zero_eq {d : ℕ}
    {φ : MonicIrreducibleOfDegree k d}
    {α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})}
    {y z : MilnorKRing (RatFunc k)}
    (hy : IsSingleResidueLift φ α y) (hz : IsSingleResidueLift φ α z) :
    milnorKPolyQuotientMk k 0 y = milnorKPolyQuotientMk k 0 z := by
  apply sub_eq_zero.mp
  rw [← map_sub, milnorKPolyQuotientMk_eq_zero_iff]
  exact hy.sub_mem_milnorKPolyFiltration_zero hz

/-- A homogeneous residue class has a unique class in the native quotient by
polynomial stage zero represented by a homogeneous single-residue lift with
the original polynomial degree bound. -/
theorem existsUnique_bounded_singleResidue_quotient_class {d : ℕ}
    (φ : MonicIrreducibleOfDegree k d) {n : ℕ}
    {α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})}
    (hα : α ∈ milnorKGrading (Polynomial k ⧸ Ideal.span {poly φ}) n) :
    ∃! q : milnorKPolyQuotient k 0,
      ∃ y ∈ milnorKGrading (RatFunc k) (n + 1),
        y ∈ milnorKPolyFiltration k d ∧ IsSingleResidueLift φ α y ∧
          milnorKPolyQuotientMk k 0 y = q := by
  obtain ⟨y, hyn, hyd, hy⟩ := exists_isSingleResidueLift_mem_milnorKPolyFiltration φ hα
  refine ⟨milnorKPolyQuotientMk k 0 y, ⟨y, hyn, hyd, hy, rfl⟩, ?_⟩
  rintro q ⟨z, _, _, hz, hq⟩
  rw [← hq]
  exact hz.milnorKPolyQuotientMk_zero_eq hy

end Stacks.Chow
