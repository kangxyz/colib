/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Colib.Util.References

/-!
# Assemble a square map from its four original corner maps

The ordinary four edge equations suffice. Keeping this construction polymorphic
avoids unfolding concrete diagram values when checking the outer arrow equation.
-/
@[expose] public section
open CategoryTheory
universe u v u₁ v₁
namespace CategoryTheory.Arrow
variable {C : Type u} [Category.{v} C] {S T : Arrow (Arrow C)}

/-- Assemble a square map against the literal functor image from the four original edges. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/ArrowSquareIso.lean:35"
  "adaptation" "Original four-corner map to the literal functor image of a square."]
def squareMapHomMk {D : Type u₁} [Category.{v₁} D] (B : C ⥤ D)
    (S : Arrow (Arrow C)) (T : Arrow (Arrow D))
    (e₀ : T.left.left ⟶ B.obj S.left.left)
    (e₁ : T.left.right ⟶ B.obj S.left.right)
    (e₂ : T.right.left ⟶ B.obj S.right.left)
    (e₃ : T.right.right ⟶ B.obj S.right.right)
    (h₀ : e₀ ≫ B.map S.left.hom = T.left.hom ≫ e₁)
    (h₁ : e₀ ≫ B.map S.hom.left = T.hom.left ≫ e₂)
    (h₂ : e₁ ≫ B.map S.hom.right = T.hom.right ≫ e₃)
    (h₃ : e₂ ≫ B.map S.right.hom = T.right.hom ≫ e₃) :
    T ⟶ B.mapArrow.mapArrow.obj S :=
  Arrow.homMk (Arrow.homMk e₀ e₁ h₀) (Arrow.homMk e₂ e₃ h₃) (by
    apply Arrow.hom_ext
    · exact h₁
    · exact h₂)

section Components
variable {D : Type u₁} [Category.{v₁} D] (B : C ⥤ D)
    (S : Arrow (Arrow C)) (T : Arrow (Arrow D))
    (e₀ : T.left.left ⟶ B.obj S.left.left)
    (e₁ : T.left.right ⟶ B.obj S.left.right)
    (e₂ : T.right.left ⟶ B.obj S.right.left)
    (e₃ : T.right.right ⟶ B.obj S.right.right)
    (h₀ : e₀ ≫ B.map S.left.hom = T.left.hom ≫ e₁)
    (h₁ : e₀ ≫ B.map S.hom.left = T.hom.left ≫ e₂)
    (h₂ : e₁ ≫ B.map S.hom.right = T.hom.right ≫ e₃)
    (h₃ : e₂ ≫ B.map S.right.hom = T.right.hom ≫ e₃)

/-- The upper component of the assembled map is the specified upper map. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/ArrowSquareIso.lean:68"
  "adaptation" "Original four-corner map to the literal functor image of a square."]
theorem squareMapHomMk_left_right :
    (squareMapHomMk B S T e₀ e₁ e₂ e₃ h₀ h₁ h₂ h₃).left.right = e₁ := rfl

/-- The terminal component of the assembled map is the specified terminal map. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/ArrowSquareIso.lean:76"
  "adaptation" "Original four-corner map to the literal functor image of a square."]
theorem squareMapHomMk_right_right :
    (squareMapHomMk B S T e₀ e₁ e₂ e₃ h₀ h₁ h₂ h₃).right.right = e₃ := rfl
end Components

end CategoryTheory.Arrow
