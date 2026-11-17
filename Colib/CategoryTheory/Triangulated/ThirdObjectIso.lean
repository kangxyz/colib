/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Colib.Util.References

/-! # Transporting the third object of a triangle -/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated.Triangle

variable {C : Type*} [Category* C] [HasShift C ℤ]

/-- Replace the third object using the specified isomorphism. The adjacent maps are
transported along its forward and inverse morphisms. -/
@[colib_tag "COL-1238"]
def ofIso₃ (T : Triangle C) {Z : C} (e : T.obj₃ ≅ Z) : Triangle C :=
  Triangle.mk T.mor₁ (T.mor₂ ≫ e.hom) (e.inv ≫ T.mor₃)

/-- The comparison with the original triangle has identity components at the first
two objects and the specified isomorphism at the third. -/
@[colib_tag "COL-1238"]
def isoOfIso₃ (T : Triangle C) {Z : C} (e : T.obj₃ ≅ Z) : T ≅ T.ofIso₃ e := by
  refine Triangle.isoMk T (T.ofIso₃ e) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_
  · change T.mor₁ ≫ 𝟙 _ = 𝟙 _ ≫ T.mor₁
    rw [Category.comp_id, Category.id_comp]
  · change T.mor₂ ≫ e.hom = 𝟙 _ ≫ (T.mor₂ ≫ e.hom)
    exact (Category.id_comp _).symm
  · let S := CategoryTheory.shiftFunctor C (1 : ℤ)
    change T.mor₃ ≫ S.map (𝟙 T.obj₁) = e.hom ≫ e.inv ≫ T.mor₃
    rw [S.map_id, Category.comp_id, e.hom_inv_id_assoc]

variable [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The transport of the third object preserves distinguished triangles. -/
@[colib_tag "COL-1238", stacks 0145 "TR1, transport through the third-object isomorphism"]
theorem ofIso₃_distinguished (T : Triangle C) {Z : C} (e : T.obj₃ ≅ Z)
    (hT : T ∈ distTriang C) : T.ofIso₃ e ∈ distTriang C :=
  (distinguished_iff_of_iso (T.isoOfIso₃ e)).1 hT

end CategoryTheory.Pretriangulated.Triangle
