/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Category.Basic

/-! # Transport of three arrows in a commuting square -/
@[expose] public section
namespace CategoryTheory
variable {C : Type*} [Category C]

/-- Replace the two left factors and the last right factor by equal arrows. -/
theorem comp3_square_transport {X₀ X₁ X₂ Y₀ Y₁ Z : C}
    (c : X₂ ⟶ Z) (d : X₀ ⟶ Y₀) (e : Y₀ ⟶ Y₁)
    {a a' : X₀ ⟶ X₁} {b b' : X₁ ⟶ X₂} {f f' : Y₁ ⟶ Z}
    (ha : a = a') (hb : b = b') (hf : f = f')
    (h : a ≫ b ≫ c = d ≫ e ≫ f) : a' ≫ b' ≫ c = d ≫ e ≫ f' := by
  subst a'
  subst b'
  subst f'
  exact h

end CategoryTheory
