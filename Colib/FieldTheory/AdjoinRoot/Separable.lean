/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Separability of the actual polynomial root field

The literal root belongs to the existing separable closure when its defining
polynomial is separable. Since that root generates the original AdjoinRoot,
every original element is separable. No new field realization is introduced.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

/-- A separable irreducible polynomial gives a separable actual root extension. -/
theorem isSeparable_of_polynomial_separable {K : Type*} [Field K]
    (q : K[X]) [Fact (Irreducible q)] (hsep : q.Separable) :
    Algebra.IsSeparable K (AdjoinRoot q) := by
  have hroot : AdjoinRoot.root q ∈ separableClosure K (AdjoinRoot q) := by
    apply mem_separableClosure_iff.mpr
    exact hsep.of_dvd (minpoly.dvd K (AdjoinRoot.root q)
      ((AdjoinRoot.aeval_eq (f := q) q).trans (AdjoinRoot.mk_self (f := q))))
  have hle : Algebra.adjoin K {AdjoinRoot.root q} ≤
      (separableClosure K (AdjoinRoot q)).toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hroot)
  rw [AdjoinRoot.adjoinRoot_eq_top] at hle
  exact ⟨fun x => mem_separableClosure_iff.mp (hle (by trivial))⟩

end AdjoinRoot
