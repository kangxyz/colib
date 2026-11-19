/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Waldhausen.Approximation.WeakImageCofinality

/-! # Regressions for cofinality of the original exact functor

The tests retain the canonical source and target maps in degree zero and in
positive degrees; they do not replace the target with the weak-image category.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.ApproximationImage
open CategoryTheory.Waldhausen.Cofinality CategoryTheory.Waldhausen.Fibration

universe u v

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationOnImage W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

-- The inclusion follows the original functor, even before imposing cofinal density.
example (n : ℕ) :
    (KMap (inclusion_exact h hF) n).comp (KMap (corestrict_exact h hF) n) = KMap hF n :=
  inclusion_KMap_comp_corestrict h hF n

variable [HasBinaryCoproducts D] [V.weq.HasTwoOutOfThreeProperty]
  (H : DenseCofiberData V (objects V F))
  (J : RowFactorization.JointData (NestedWeakEquivalences.refl W))
  (J' : RowFactorization.JointData (NestedWeakEquivalences.refl V))
  (s : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl V) J')

-- The equivalence is the existing K-map, not merely an abstract group isomorphism.
example (n : ℕ) (x : W.K (n + 1)) :
    originalKEquivOfDense h hF H J J' s n x = KMap hF (n + 1) x :=
  rfl

example (n : ℕ) :
    (KMap hF n).range = (KMap (changeWeak_exact H.grading.nested) n).ker :=
  original_range_KMap_of_dense h hF H J J' s n

example :
    Function.Injective (KMap hF 0) ∧
      (KMap hF 0).range = (KMap (changeWeak_exact H.grading.nested) 0).ker ∧
      Function.Surjective (KMap (changeWeak_exact H.grading.nested) 0) :=
  original_KZero_exact_of_dense h hF H J J' s
