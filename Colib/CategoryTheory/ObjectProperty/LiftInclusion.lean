/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Forgetting a further property of an original full-subcategory functor

A lift to a smaller object property followed by the original inclusion is the unchanged
functor to the larger full subcategory. This literal identity avoids expanding its objects.
-/
@[expose] public section
open CategoryTheory
universe u v w z
namespace CategoryTheory.ObjectProperty
variable {A : Type u} [Category.{v} A] {B : Type w} [Category.{z} B]

/-- Forget only the additional property of the original functor, preserving every map literally. -/
@[colib_ref "quillen" "Quillen/Aglib/CategoryTheory/ObjectProperty/LiftInclusion.lean:23"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem lift_comp_ιOfLE (P Q : CategoryTheory.ObjectProperty B) (h : P ≤ Q)
    (F : A ⥤ Q.FullSubcategory) (hF : ∀ X, P (F.obj X).obj) :
    P.lift (F ⋙ Q.ι) hF ⋙ CategoryTheory.ObjectProperty.ιOfLE h = F := rfl

/-- The same identity retains a specified precomposition without reassociating large functors. -/
@[colib_ref "quillen" "Quillen/Aglib/CategoryTheory/ObjectProperty/LiftInclusion.lean:28"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem lift_comp_ιOfLE_comp {C : Type*} [Category* C]
    (P Q : CategoryTheory.ObjectProperty B) (h : P ≤ Q)
    (I : A ⥤ C) (F : C ⥤ Q.FullSubcategory) (hF : ∀ X, P (F.obj (I.obj X)).obj) :
    P.lift (I ⋙ F ⋙ Q.ι) hF ⋙ CategoryTheory.ObjectProperty.ιOfLE h = I ⋙ F := rfl

end CategoryTheory.ObjectProperty

