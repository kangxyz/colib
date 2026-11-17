/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Shift.CommShiftTwoFullyFaithfulData
public import Colib.CategoryTheory.Shift.CommShiftTwoPrecompPostcomp
import Colib.Util.References

/-! # Fixed-parameter comparisons of signed bifunctor shifts

The reflected shift data and the data obtained by precomposition and
postcomposition give specific one-variable structures in both slots.
-/

attribute [colib_tag "COL-1237",
  colib_ref "mathlib_stable_localization_pin" "Mathlib/CategoryTheory/Shift/CommShift.lean:533-589"
    "ingredient" "One-variable shift reflection along a fully faithful functor"]
  CategoryTheory.Functor.CommShift₂.ofFullyFaithfulInt_commShiftObj

attribute [colib_tag "COL-1237"]
  CategoryTheory.Functor.CommShift₂.ofFullyFaithfulInt
  CategoryTheory.Functor.CommShift₂.ofFullyFaithfulInt_commShiftFlipObj
  CategoryTheory.Functor.CommShift₂.postcompInt_precomp_commShiftObj
  CategoryTheory.Functor.CommShift₂.postcompInt_precomp_commShiftFlipObj
