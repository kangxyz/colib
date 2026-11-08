/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.RingTheory.KTheory.MilnorK.SingleResidueFiltration
public import Colib.RingTheory.KTheory.MilnorK.Norm.FiniteReciprocity

/-!
# Bounded finite residue prescription, including infinity

A finite family of homogeneous residue classes at distinct monic irreducible
polynomials has a simultaneous homogeneous lift. The lift belongs to the
original polynomial filtration at any bound for the degrees of those points.
There are no other finite residues.

Prescribing the residue at infinity is possible exactly when its sum with the
existing simple norms of the prescribed finite residues is zero. This combines
native single-residue lifting with the existing finite reciprocity theorem;
it does not define a total residue, a total norm, or another point model.
The bounded lift determines a unique class modulo the native stage zero.

The single-residue input is Stacks' `exists_isSingleResidueLift'`, and the
infinity criterion uses the maintained `Norm.FiniteReciprocity` endpoint.
This is a finite-data consequence of Milnor's rational-function exactness
argument, with the native weak polynomial-degree bound retained explicitly.
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree

variable {k : Type u} [Field k] {ι : Type v}

attribute [local instance] Ideal.Quotient.field

/-- Prescribed homogeneous finite residues have a homogeneous simultaneous
lift at the original degree bound, with no additional finite residues. -/
theorem exists_bounded_finiteResidue_lift
    (s : Finset ι) (d : ι → ℕ) (ψ : ∀ i, MonicIrreducibleOfDegree k (d i))
    (hinj : Set.InjOn (fun i ↦ poly (ψ i)) (s : Set ι))
    (n N : ℕ) (hd : ∀ i ∈ s, d i ≤ N)
    (α : ∀ i, MilnorKTheory (Polynomial k ⧸ Ideal.span {poly (ψ i)}) n) :
    ∃ y : MilnorKTheory (RatFunc k) (n + 1),
      (y : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k N ∧
      (∀ i ∈ s, monicIrreducibleResidue (ψ i) y = α i) ∧
      (∀ (e : ℕ) (χ : MonicIrreducibleOfDegree k e),
        (∀ i ∈ s, poly χ ≠ poly (ψ i)) → monicIrreducibleResidue χ y = 0) := by
  classical
  choose z hzn hzd hz using fun i ↦
    exists_isSingleResidueLift_mem_milnorKPolyFiltration (ψ i) (α i).2
  refine ⟨⟨∑ i ∈ s, z i, (milnorKGrading (RatFunc k) (n + 1)).sum_mem
    (fun i _ ↦ hzn i)⟩, ?_, ?_, ?_⟩
  · exact (milnorKPolyFiltration k N).sum_mem
      (fun i hi ↦ milnorKPolyFiltration_mono (hd i hi) (hzd i))
  · intro i hi
    change monicIrreducibleResidue (ψ i) (∑ j ∈ s, z j) = α i
    rw [map_sum]
    refine (Finset.sum_eq_single i ?_ ?_).trans (hz i).1
    · intro j hj hji
      exact (hz j).2 _ (ψ i) (fun h ↦ hji (hinj hj hi h.symm))
    · intro hnot
      exact (hnot hi).elim
  · intro e χ hχ
    change monicIrreducibleResidue χ (∑ i ∈ s, z i) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero (fun i hi ↦ (hz i).2 e χ (hχ i hi))

/-- Two classes with identical finite residue data and no other residues differ
by the native stage zero. Homogeneity and a degree bound are not needed. -/
theorem sub_mem_milnorKPolyFiltration_zero_of_finite_residue_data
    (s : Finset ι) (d : ι → ℕ) (ψ : ∀ i, MonicIrreducibleOfDegree k (d i))
    (y z : MilnorKRing (RatFunc k))
    (hresidue : ∀ i ∈ s, monicIrreducibleResidue (ψ i) y =
      monicIrreducibleResidue (ψ i) z)
    (hy : ∀ (e : ℕ) (χ : MonicIrreducibleOfDegree k e),
      (∀ i ∈ s, poly χ ≠ poly (ψ i)) → monicIrreducibleResidue χ y = 0)
    (hz : ∀ (e : ℕ) (χ : MonicIrreducibleOfDegree k e),
      (∀ i ∈ s, poly χ ≠ poly (ψ i)) → monicIrreducibleResidue χ z = 0) :
    y - z ∈ milnorKPolyFiltration k 0 := by
  apply mem_milnorKPolyFiltration_zero_of_forall_monicIrreducibleResidue_eq_zero
  intro e χ
  by_cases h : ∃ i ∈ s, poly χ = poly (ψ i)
  · obtain ⟨i, hi, hp⟩ := h
    apply monicIrreducibleResidue_eq_zero_of_poly_eq hp.symm
    rw [map_sub, hresidue i hi, sub_self]
  · have hne : ∀ i ∈ s, poly χ ≠ poly (ψ i) := fun i hi hp ↦ h ⟨i, hi, hp⟩
    rw [map_sub, hy _ χ hne, hz _ χ hne, sub_self]

/-- The exact obstruction to prescribing infinity along with bounded finite
residue data is the sum of the original simple norms. Residue degree zero is
included, and the prescribed infinity class need not be assumed homogeneous. -/
theorem exists_bounded_finiteResidue_lift_with_infinity_iff
    (s : Finset ι) (d : ι → ℕ) (ψ : ∀ i, MonicIrreducibleOfDegree k (d i))
    (hinj : Set.InjOn (fun i ↦ poly (ψ i)) (s : Set ι))
    (n N : ℕ) (hd : ∀ i ∈ s, d i ≤ N)
    (α : ∀ i, MilnorKTheory (Polynomial k ⧸ Ideal.span {poly (ψ i)}) n)
    (β : MilnorKRing k) :
    (∃ y : MilnorKTheory (RatFunc k) (n + 1),
      (y : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k N ∧
      (∀ i ∈ s, monicIrreducibleResidue (ψ i) y = α i) ∧
      (∀ (e : ℕ) (χ : MonicIrreducibleOfDegree k e),
        (∀ i ∈ s, poly χ ≠ poly (ψ i)) → monicIrreducibleResidue χ y = 0) ∧
      infinityResidueRing k y = β) ↔
      (∑ i ∈ s, simpleMilnorNorm (ψ i) (α i)) + β = 0 := by
  constructor
  · rintro ⟨y, _, hres, hsupp, hInfinity⟩
    rw [sum_simpleMilnorNorm_eq_neg_infinityResidueRing_of_residues
      s d ψ hinj (fun i ↦ α i) y hres hsupp, hInfinity, neg_add_cancel]
  · intro hβ
    obtain ⟨y, hy, hres, hsupp⟩ :=
      exists_bounded_finiteResidue_lift s d ψ hinj n N hd α
    refine ⟨y, hy, hres, hsupp, ?_⟩
    have hsum : (∑ i ∈ s, simpleMilnorNorm (ψ i) (α i)) + infinityResidueRing k y = 0 := by
      rw [sum_simpleMilnorNorm_eq_neg_infinityResidueRing_of_residues
        s d ψ hinj (fun i ↦ α i) y hres hsupp, neg_add_cancel]
    exact (add_left_cancel (hβ.trans hsum.symm)).symm

/-- Compatible finite and infinity residue data determine a unique class in the
native quotient by stage zero, represented by a homogeneous bounded lift. -/
theorem existsUnique_bounded_finiteResidue_quotient_class
    (s : Finset ι) (d : ι → ℕ) (ψ : ∀ i, MonicIrreducibleOfDegree k (d i))
    (hinj : Set.InjOn (fun i ↦ poly (ψ i)) (s : Set ι))
    (n N : ℕ) (hd : ∀ i ∈ s, d i ≤ N)
    (α : ∀ i, MilnorKTheory (Polynomial k ⧸ Ideal.span {poly (ψ i)}) n)
    (β : MilnorKRing k)
    (hβ : (∑ i ∈ s, simpleMilnorNorm (ψ i) (α i)) + β = 0) :
    ∃! q : milnorKPolyQuotient k 0,
      ∃ y : MilnorKTheory (RatFunc k) (n + 1),
        (y : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k N ∧
        (∀ i ∈ s, monicIrreducibleResidue (ψ i) y = α i) ∧
        (∀ (e : ℕ) (χ : MonicIrreducibleOfDegree k e),
          (∀ i ∈ s, poly χ ≠ poly (ψ i)) → monicIrreducibleResidue χ y = 0) ∧
        infinityResidueRing k y = β ∧ milnorKPolyQuotientMk k 0 y = q := by
  obtain ⟨y, hy, hres, hsupp, hInfinity⟩ :=
    (exists_bounded_finiteResidue_lift_with_infinity_iff s d ψ hinj n N hd α β).mpr hβ
  refine ⟨milnorKPolyQuotientMk k 0 y, ⟨y, hy, hres, hsupp, hInfinity, rfl⟩, ?_⟩
  rintro q ⟨z, _, hzres, hzsupp, _, hq⟩
  rw [← hq]
  apply sub_eq_zero.mp
  rw [← map_sub, milnorKPolyQuotientMk_eq_zero_iff]
  exact sub_mem_milnorKPolyFiltration_zero_of_finite_residue_data s d ψ z y
    (fun i hi ↦ (hzres i hi).trans (hres i hi).symm) hzsupp hsupp

end Stacks.Chow

attribute [colib_tag "COL-0317"]
  Stacks.Chow.exists_bounded_finiteResidue_lift_with_infinity_iff
  Stacks.Chow.existsUnique_bounded_finiteResidue_quotient_class

attribute [colib_ref "axiom_stacks_milnor_norm_5ed82d14"
  "SimpleNorm.lean, exists_isSingleResidueLift' and simpleMilnorNorm_eq" "ingredient"
  "Native homogeneous single-residue lifts and the norm = negative infinity identity;
   finite prescription, bound and compatibility are derived here."]
  Stacks.Chow.exists_bounded_finiteResidue_lift_with_infinity_iff
