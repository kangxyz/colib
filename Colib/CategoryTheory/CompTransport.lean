/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Category.Basic

/-! # Transport of a composition through an equality of its first arrow -/
@[expose] public section
namespace CategoryTheory
variable {C : Type*} [Category C]

/-- Replace the first arrow of a verified composition by an equal arrow. -/
theorem comp_transport {X Y Z : C} (g : Y ⟶ Z) {f f' : X ⟶ Y} {h : X ⟶ Z}
    (hf : f = f') (hc : f ≫ g = h) : f' ≫ g = h := by
  subst f'
  exact hc

end CategoryTheory
