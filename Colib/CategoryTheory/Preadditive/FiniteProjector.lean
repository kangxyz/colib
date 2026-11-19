/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-! # Ordered complementary projectors for commuting idempotents -/

@[expose] public section

namespace CategoryTheory
open Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {X : C} {ι : Type*}

/-- Compose the complements in a fixed list order; the empty product is the identity. -/
def complementaryProjector (e : ι → (X ⟶ X)) : List ι → (X ⟶ X)
  | [] => 𝟙 X
  | i :: l => (𝟙 X - e i) ≫ complementaryProjector e l

/-- An included idempotent is annihilated by the joint complementary projector. -/
theorem comp_complementaryProjector_eq_zero (e : ι → (X ⟶ X))
    (hid : ∀ i, e i ≫ e i = e i)
    (hcomm : ∀ i j, e i ≫ e j = e j ≫ e i)
    (l : List ι) (j : ι) (hj : j ∈ l) :
    e j ≫ complementaryProjector e l = 0 := by
  induction l with
  | nil => simp at hj
  | cons i l ih =>
    rcases List.mem_cons.mp hj with h | h
    · subst j
      simp only [complementaryProjector, ← Category.assoc, Preadditive.comp_sub,
        Category.comp_id, hid, sub_self, zero_comp]
    · have he : e j ≫ (𝟙 X - e i) = (𝟙 X - e i) ≫ e j := by
        simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
          Category.id_comp, hcomm j i]
      rw [complementaryProjector, ← Category.assoc, he, Category.assoc, ih h, comp_zero]

/-- On a quotient killing each idempotent, the joint complement acts as the identity. -/
theorem complementaryProjector_comp (e : ι → (X ⟶ X)) {Y : C} (p : X ⟶ Y)
    (hp : ∀ i, e i ≫ p = 0) (l : List ι) :
    complementaryProjector e l ≫ p = p := by
  induction l with
  | nil => simp [complementaryProjector]
  | cons i l ih =>
    simp only [complementaryProjector, Category.assoc, ih, Preadditive.sub_comp,
      Category.id_comp, hp, sub_zero]

end CategoryTheory
