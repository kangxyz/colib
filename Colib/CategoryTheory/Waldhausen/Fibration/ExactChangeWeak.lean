/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory

/-!
# Exactness into an enlarged weak class

The original functor, cofibration maps and displayed pushout squares are unchanged.
Only its target weak-equivalence proof is composed with the given class inclusion.
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits
universe u v u' v'
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {V : Structure C} {W : Structure D} {F : C ⥤ D}

/-- The same exact functor is exact into the original enlarged target weak class. -/
@[colib_ref "quillen" "Quillen/Waldhausen/Fibration/ExactChangeWeak.lean:25-31"
  "adaptation" "The same exact functor into the original enlarged target weak class"]
theorem IsExact.changeWeakTarget (hF : IsExact V.cof V.weq W.cof W.weq F)
    (N : Fibration.NestedWeakEquivalences W) :
    IsExact V.cof V.weq N.coarse.cof N.coarse.weq F where
  zero := hF.zero
  cofibration f hf := by rw [N.cof_eq]; exact hF.cofibration f hf
  weak f hf := N.le_weq (F.map f) (hF.weak f hf)
  pushout := hF.pushout

end CategoryTheory.Waldhausen
