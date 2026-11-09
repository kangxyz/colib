/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Finite coprime splitting over an arbitrary field

Adjoin the finite root set one element at a time. At every step, the minimal
polynomial of the new root divides the coefficient image of one of the original
small polynomials. Its positive degree is strictly smaller than the given prime.
The tower law therefore preserves coprimality.

In particular the full native splitting field of the literal product, rather
than just a Sylow fixed subfield, has prime-to-prime degree. No perfectness or
separability is required, including for the auxiliary extension.
-/

@[expose] public noncomputable section

namespace IntermediateField

open Polynomial

variable {k M : Type*} [Field k] [Field M] [Algebra k M]

/-- A finite set of roots of small nonzero polynomials generates an extension
of degree coprime to the specified prime. The ambient extension is only assumed
finite; it need not be normal or separable. -/
theorem coprime_finrank_adjoin_finset_of_small_polynomial
    [FiniteDimensional k M] (ell : ℕ) (hell : ell.Prime) (t : Finset M)
    (ht : ∀ x ∈ t, ∃ q : k[X],
      q ≠ 0 ∧ q.natDegree < ell ∧ aeval x q = 0) :
    ell.Coprime (Module.finrank k (adjoin k (t : Set M))) := by
  classical
  refine induction_on_adjoin_finset t
    (motive := fun S => ell.Coprime (Module.finrank k S)) ?_ ?_
  · simp
  · intro S x hx hS
    obtain ⟨q, hq, hqd, hxq⟩ := ht x hx
    have hxint : IsIntegral S x := IsIntegral.of_finite S x
    have hmin : minpoly S x ∣ q.map (algebraMap k S) :=
      minpoly.dvd S x (by rwa [aeval_map_algebraMap])
    have hpos : 0 < (minpoly S x).natDegree := minpoly.natDegree_pos hxint
    have hlt : (minpoly S x).natDegree < ell := by
      have hle := natDegree_le_of_dvd hmin (Polynomial.map_ne_zero hq)
      rw [natDegree_map] at hle
      exact hle.trans_lt hqd
    have hcop : ell.Coprime (Module.finrank S S⟮x⟯) := by
      rw [adjoin.finrank hxint]
      exact hell.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hpos hlt)
    change ell.Coprime (Module.finrank k S⟮x⟯)
    rw [← Module.finrank_mul_finrank k S S⟮x⟯]
    exact hS.mul_right hcop

end IntermediateField

namespace Polynomial

variable {k : Type*} [Field k]

/-- The native splitting field of the product of finitely many nonzero
polynomials of degree below a prime has degree coprime to that prime. -/
theorem coprime_finrank_splittingField_prod_of_natDegree_lt
    (ell : ℕ) (hell : ell.Prime) (s : Finset k[X])
    (hne : ∀ q ∈ s, q ≠ 0) (hsmall : ∀ q ∈ s, q.natDegree < ell) :
    ell.Coprime (Module.finrank k (∏ q ∈ s, q).SplittingField) := by
  classical
  let f : k[X] := ∏ q ∈ s, q
  let M := f.SplittingField
  have hf : f ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  let t : Finset M := (f.aroots M).toFinset
  have ht : (t : Set M) = f.rootSet M := (rootSet_def f M).symm
  have hgen : IntermediateField.adjoin k (t : Set M) = ⊤ := by
    rw [ht]
    exact (isSplittingField_iff_intermediateField.mp
      (inferInstance : IsSplittingField k M f)).2
  have hroot : ∀ x ∈ t, ∃ q : k[X],
      q ≠ 0 ∧ q.natDegree < ell ∧ aeval x q = 0 := by
    intro x hx
    have hxroot : x ∈ f.rootSet M := by
      rw [← ht]
      exact hx
    change x ∈ (s.prod id).rootSet M at hxroot
    rw [rootSet_prod id s hf] at hxroot
    obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hxroot
    exact ⟨q, hne q hq, hsmall q hq, aeval_eq_zero_of_mem_rootSet hxq⟩
  have hcop := IntermediateField.coprime_finrank_adjoin_finset_of_small_polynomial
    ell hell t hroot
  rw [hgen, IntermediateField.finrank_top'] at hcop
  exact hcop

end Polynomial

namespace IntermediateField

open Polynomial

variable {k : Type*} [Field k]

/-- Characteristic-free finite coprime splitting in an actual intermediate
field of the native product splitting field. The witness is its top field. -/
theorem exists_coprime_splitting_field_of_finset_arbitrary
    (ell : ℕ) [Fact ell.Prime] (s : Finset k[X])
    (hne : ∀ q ∈ s, q ≠ 0) (hsmall : ∀ q ∈ s, q.natDegree < ell) :
    ∃ S : IntermediateField k (∏ q ∈ s, q).SplittingField,
      FiniteDimensional k S ∧ ell.Coprime (Module.finrank k S) ∧
      ∀ q ∈ s, (q.map (algebraMap k S)).Splits := by
  classical
  let f : k[X] := ∏ q ∈ s, q
  have hf : f ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  refine ⟨⊤, inferInstance, ?_, ?_⟩
  · simpa only [IntermediateField.finrank_top'] using
      coprime_finrank_splittingField_prod_of_natDegree_lt ell Fact.out s hne hsmall
  · intro q hq
    apply splits_of_splits
      ((SplittingField.splits f).of_dvd (Polynomial.map_ne_zero hf)
        (Polynomial.map_dvd (algebraMap k f.SplittingField)
          (Finset.dvd_prod_of_mem id hq)))
    intro x hx
    exact Set.mem_univ x

end IntermediateField
