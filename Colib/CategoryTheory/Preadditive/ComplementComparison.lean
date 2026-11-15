/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Comparing complements through additive functors -/

@[expose] public section

namespace CategoryTheory.Functor

/-- Two intertwining squares induce an intertwining square for the complements of their
composites. -/
theorem map_complement_comp_of_intertwining
    {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
    (H : C₁ ⥤ C₃) (F : C₂ ⥤ C₃) [H.Additive] [F.Additive]
    {R R' : C₁} {U U' : C₂}
    {x : R ⟶ R'} {y : R' ⟶ R} {p : U ⟶ U'} {i : U' ⟶ U}
    {v : H.obj R ⟶ F.obj U} {v' : H.obj R' ⟶ F.obj U'}
    (hx : H.map x ≫ v' = v ≫ F.map p) (hy : H.map y ≫ v = v' ≫ F.map i)
    {s : R ⟶ R} {t : U ⟶ U} (hs : s = x ≫ y) (ht : t = p ≫ i) :
    H.map (𝟙 R - s) ≫ v = v ≫ F.map (𝟙 U - t) := by
  have h : H.map s ≫ v = v ≫ F.map t := by
    rw [hs, ht, H.map_comp, F.map_comp, Category.assoc, hy, ← Category.assoc (H.map x),
      hx, Category.assoc]
  simp only [H.map_sub, F.map_sub, H.map_id, F.map_id, Preadditive.sub_comp,
    Preadditive.comp_sub, Category.id_comp, Category.comp_id, h]

end CategoryTheory.Functor
