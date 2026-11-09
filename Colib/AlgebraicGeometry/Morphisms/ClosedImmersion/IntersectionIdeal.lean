/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Kernel of an actual closed-subscheme intersection

The native ideal-sheaf and closed-immersion universal properties give the exact
sum ideal, without taking radicals. No new model of a closed subscheme is used.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Motivic/Aglib/AlgebraicGeometry/Morphisms/ClosedImmersion/Kernel.lean,
Git blob a1d23ccc5a03138555d679e319b5c1b5f93ac081. This supporting lemma
has no claim to finite Tor, regularity, or intersection-cycle associativity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The actual ideal of a Cartesian intersection of closed immersions is their sum. -/
theorem ker_comp_eq_sup_of_isPullback {W D T P : Scheme.{u}}
    (a : W ⟶ D) (b : W ⟶ T) (i : D ⟶ P) (j : T ⟶ P)
    [IsClosedImmersion i] [IsClosedImmersion j] (sq : IsPullback a b i j) :
    (a ≫ i).ker = i.ker ⊔ j.ker := by
  let I := i.ker ⊔ j.ker
  apply le_antisymm
  · have hi : i.ker ≤ I.subschemeι.ker := by
      rw [I.ker_subschemeι]
      exact le_sup_left
    have hj : j.ker ≤ I.subschemeι.ker := by
      rw [I.ker_subschemeι]
      exact le_sup_right
    let d := IsClosedImmersion.lift i I.subschemeι hi
    let t := IsClosedImmersion.lift j I.subschemeι hj
    have hd : d ≫ i = I.subschemeι := IsClosedImmersion.lift_fac _ _ _
    have ht : t ≫ j = I.subschemeι := IsClosedImmersion.lift_fac _ _ _
    let w := sq.lift d t (hd.trans ht.symm)
    have hw : w ≫ (a ≫ i) = I.subschemeι := by
      rw [← Category.assoc, IsPullback.lift_fst, hd]
    have hk := Scheme.Hom.le_ker_comp w (a ≫ i)
    rwa [hw, I.ker_subschemeι] at hk
  · exact sup_le (Scheme.Hom.le_ker_comp a i)
      (sq.w.symm ▸ Scheme.Hom.le_ker_comp b j)

end AlgebraicGeometry.Scheme.Hom
