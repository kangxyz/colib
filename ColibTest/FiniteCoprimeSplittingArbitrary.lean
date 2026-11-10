module

import Colib.FieldTheory.FiniteCoprimeSplittingArbitrary

noncomputable section

open Polynomial IntermediateField

universe u v

/-- Independent field universes and arbitrary characteristic are allowed. -/
example {k : Type u} {M : Type v} [Field k] [Field M] [Algebra k M]
    [FiniteDimensional k M] (ell : ℕ) (hell : ell.Prime) (t : Finset M)
    (ht : ∀ x ∈ t, ∃ q : k[X], q ≠ 0 ∧ q.natDegree < ell ∧ aeval x q = 0) :
    ell.Coprime (Module.finrank k (adjoin k (t : Set M))) :=
  coprime_finrank_adjoin_finset_of_small_polynomial ell hell t ht

/-- No separability or perfectness is assumed on the entire polynomial family. -/
example {k : Type u} [Field k] (ell : ℕ) [Fact ell.Prime]
    (s : Finset k[X]) (hne : ∀ q ∈ s, q ≠ 0)
    (hsmall : ∀ q ∈ s, q.natDegree < ell) :
    ∃ S : IntermediateField k (∏ q ∈ s, q).SplittingField,
      FiniteDimensional k S ∧ ell.Coprime (Module.finrank k S) ∧
      ∀ q ∈ s, (q.map (algebraMap k S)).Splits :=
  exists_coprime_splitting_field_of_finset_arbitrary ell s hne hsmall

/-- In characteristic two, the quadratic can be inseparable. Its actual splitting
field nevertheless has degree prime to three. The parameter is unrestricted. -/
example {k : Type u} [Field k] [CharP k 2] (a : k) :
    Nat.Coprime 3 (Module.finrank k
      (∏ q ∈ ({X ^ 2 - C a} : Finset k[X]), q).SplittingField) := by
  classical
  have h := coprime_finrank_splittingField_prod_of_natDegree_lt
    3 (by decide) ({X ^ 2 - C a} : Finset k[X])
    (by
      intro q hq
      have hq' : q = X ^ 2 - C a := Finset.mem_singleton.mp hq
      subst q
      exact (monic_X_pow_sub_C a (by decide : (2 : ℕ) ≠ 0)).ne_zero)
    (by
      intro q hq
      have hq' : q = X ^ 2 - C a := Finset.mem_singleton.mp hq
      subst q
      rw [natDegree_X_pow_sub_C]
      decide)
  exact h

/-- The empty family is covered by the same theorem, without a nonempty premise. -/
example {k : Type u} [Field k] (ell : ℕ) (hell : ell.Prime) :
    ell.Coprime (Module.finrank k
      (∏ q ∈ (∅ : Finset k[X]), q).SplittingField) := by
  classical
  exact coprime_finrank_splittingField_prod_of_natDegree_lt ell hell (∅ : Finset k[X])
      (by simp) (by simp)

end
