module

import Colib.RingTheory.KTheory.MilnorK.FiniteResiduePrescription

open Stacks.Chow MonicIrreducibleOfDegree

universe u v

variable (k : Type u) [Field k] {ι : Type v}

attribute [local instance] Ideal.Quotient.field

-- Native degree-zero residue classes are allowed; no characteristic restriction is imposed.
example (s : Finset ι) (d : ι → ℕ) (ψ : ∀ i, MonicIrreducibleOfDegree k (d i))
    (hinj : Set.InjOn (fun i ↦ poly (ψ i)) (s : Set ι))
    (N : ℕ) (hd : ∀ i ∈ s, d i ≤ N)
    (α : ∀ i, MilnorKTheory (Polynomial k ⧸ Ideal.span {poly (ψ i)}) 0)
    (β : MilnorKRing k) :
    (∃ y : MilnorKTheory (RatFunc k) 1,
      (y : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k N ∧
      (∀ i ∈ s, monicIrreducibleResidue (ψ i) y = α i) ∧
      (∀ (e : ℕ) (χ : MonicIrreducibleOfDegree k e),
        (∀ i ∈ s, poly χ ≠ poly (ψ i)) → monicIrreducibleResidue χ y = 0) ∧
      infinityResidueRing k y = β) ↔
      (∑ i ∈ s, simpleMilnorNorm (ψ i) (α i)) + β = 0 :=
  exists_bounded_finiteResidue_lift_with_infinity_iff s d ψ hinj 0 N hd α β

-- The empty finite support admits exactly the zero infinity residue, even at bound zero.
example (n : ℕ) (β : MilnorKRing k) :
    (∃ y : MilnorKTheory (RatFunc k) (n + 1),
      (y : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k 0 ∧
      (∀ (e : ℕ) (χ : MonicIrreducibleOfDegree k e), monicIrreducibleResidue χ y = 0) ∧
      infinityResidueRing k y = β) ↔ β = 0 := by
  simpa using exists_bounded_finiteResidue_lift_with_infinity_iff
    (k := k) (∅ : Finset PEmpty) (fun i ↦ i.elim) (fun i ↦ i.elim)
    (fun i ↦ i.elim) n 0 (fun i ↦ i.elim) (fun i ↦ i.elim) β

-- Compatible data determine a quotient class, not a unique rational-function class.
example (s : Finset ι) (d : ι → ℕ) (ψ : ∀ i, MonicIrreducibleOfDegree k (d i))
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
        infinityResidueRing k y = β ∧ milnorKPolyQuotientMk k 0 y = q :=
  existsUnique_bounded_finiteResidue_quotient_class s d ψ hinj n N hd α β hβ

-- Uniqueness modulo F0 needs neither homogeneous lifts nor distinct indexing.
example (s : Finset ι) (d : ι → ℕ) (ψ : ∀ i, MonicIrreducibleOfDegree k (d i))
    (y z : MilnorKRing (RatFunc k))
    (hres : ∀ i ∈ s, monicIrreducibleResidue (ψ i) y = monicIrreducibleResidue (ψ i) z)
    (hy : ∀ (e : ℕ) (χ : MonicIrreducibleOfDegree k e),
      (∀ i ∈ s, poly χ ≠ poly (ψ i)) → monicIrreducibleResidue χ y = 0)
    (hz : ∀ (e : ℕ) (χ : MonicIrreducibleOfDegree k e),
      (∀ i ∈ s, poly χ ≠ poly (ψ i)) → monicIrreducibleResidue χ z = 0) :
    y - z ∈ milnorKPolyFiltration k 0 :=
  sub_mem_milnorKPolyFiltration_zero_of_finite_residue_data s d ψ y z hres hy hz
