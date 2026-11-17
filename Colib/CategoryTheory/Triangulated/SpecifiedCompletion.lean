/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Prescribing the third map between distinguished triangles -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- The second square determines its third component when there are no morphisms
from the shifted first object to the third object of the target. -/
theorem Triangle.hom_ext₃ (T : Triangle C) (hT : T ∈ distTriang C)
    {A : C} (h : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ A))
    {a b : T.obj₃ ⟶ A} (hab : T.mor₂ ≫ a = T.mor₂ ≫ b) :
    a = b := by
  have hz : T.mor₂ ≫ (a - b) = 0 := by
    rw [Preadditive.comp_sub, hab, sub_self]
  obtain ⟨g, hg⟩ := T.yoneda_exact₃ hT _ hz
  exact sub_eq_zero.mp (hg.trans (by rw [h.elim g 0, comp_zero]))

/-- Two commuting squares of distinguished triangles determine a triangle morphism
with the specified third component under the corresponding vanishing. -/
def triangleMorphismOfSubsingleton {T T' : Triangle C}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (h : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃))
    (a : T.obj₁ ⟶ T'.obj₁) (b : T.obj₂ ⟶ T'.obj₂) (c : T.obj₃ ⟶ T'.obj₃)
    (h₁ : T.mor₁ ≫ b = a ≫ T'.mor₁) (h₂ : T.mor₂ ≫ c = b ≫ T'.mor₂) :
    T ⟶ T' where
  hom₁ := a
  hom₂ := b
  hom₃ := c
  comm₁ := h₁
  comm₂ := h₂
  comm₃ := by
    obtain ⟨c', hc', hd'⟩ := complete_distinguished_triangle_morphism T T' hT hT' a b h₁
    have hc : c = c' := T.hom_ext₃ hT h (h₂.trans hc'.symm)
    rw [hc]
    exact hd'

end CategoryTheory.Pretriangulated
