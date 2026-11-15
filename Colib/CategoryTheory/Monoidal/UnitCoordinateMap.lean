/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Monoidal.Functor
/-! # Actual unit-coordinate insertion under a lax monoidal functor -/
@[expose] public section
open CategoryTheory MonoidalCategory
namespace CategoryTheory.Functor.LaxMonoidal
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

/-- The genuine unit-coordinate tensor map is carried through the original
lax unit and tensorator. No structure map is assumed invertible. -/
theorem map_unitCoordinate (F : C ⥤ D) [F.LaxMonoidal] {X Y Z : C}
    (a : X ⟶ Y) (b : 𝟙_ C ⟶ Z) :
    F.map ((ρ_ X).inv ≫ (a ⊗ₘ b)) =
      (ρ_ (F.obj X)).inv ≫ (F.map a ⊗ₘ (ε F ≫ F.map b)) ≫ μ F Y Z := by
  rw [F.map_comp, ← right_unitality_inv F X, Category.assoc, Category.assoc, ← μ_natural]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp]

end CategoryTheory.Functor.LaxMonoidal
