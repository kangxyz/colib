/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Colib.Util.References

/-!
# Square isomorphisms into an actual functor image

The four original component isomorphisms and four local edge equations assemble
an isomorphism into the literal functor image of a square. Its inverse components
are the specified original inverses.
-/
@[expose] public section
open CategoryTheory
universe u v u' v'
namespace CategoryTheory.Arrow
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (B : C ⥤ D) (S : Arrow (Arrow C)) (T : Arrow (Arrow D))
    (e₀ : T.left.left ≅ B.obj S.left.left)
    (e₁ : T.left.right ≅ B.obj S.left.right)
    (e₂ : T.right.left ≅ B.obj S.right.left)
    (e₃ : T.right.right ≅ B.obj S.right.right)
    (h₀ : e₀.hom ≫ B.map S.left.hom = T.left.hom ≫ e₁.hom)
    (h₁ : e₀.hom ≫ B.map S.hom.left = T.hom.left ≫ e₂.hom)
    (h₂ : e₁.hom ≫ B.map S.hom.right = T.hom.right ≫ e₃.hom)
    (h₃ : e₂.hom ≫ B.map S.right.hom = T.right.hom ≫ e₃.hom)

/-- Assemble the actual square isomorphism against the literal image square. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/ArrowSquareMapIso.lean:33"
  "adaptation" "Original four specified factor isomorphisms and literal total-cone target."]
def squareMapIsoMk : T ≅ B.mapArrow.mapArrow.obj S :=
  Arrow.isoMk (Arrow.isoMk e₀ e₁ h₀) (Arrow.isoMk e₂ e₃ h₃) (by
    apply Arrow.hom_ext
    · exact h₁
    · exact h₂)

/-- The inverse source component is exactly the specified inverse. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/ArrowSquareMapIso.lean:40"
  "adaptation" "Original four specified factor isomorphisms and literal total-cone target."]
theorem squareMapIsoMk_inv_left_left :
    (squareMapIsoMk B S T e₀ e₁ e₂ e₃ h₀ h₁ h₂ h₃).inv.left.left = e₀.inv := rfl

/-- The inverse upper component is exactly the specified inverse. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/ArrowSquareMapIso.lean:44"
  "adaptation" "Original four specified factor isomorphisms and literal total-cone target."]
theorem squareMapIsoMk_inv_left_right :
    (squareMapIsoMk B S T e₀ e₁ e₂ e₃ h₀ h₁ h₂ h₃).inv.left.right = e₁.inv := rfl

/-- The inverse lower component is exactly the specified inverse. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/ArrowSquareMapIso.lean:48"
  "adaptation" "Original four specified factor isomorphisms and literal total-cone target."]
theorem squareMapIsoMk_inv_right_left :
    (squareMapIsoMk B S T e₀ e₁ e₂ e₃ h₀ h₁ h₂ h₃).inv.right.left = e₂.inv := rfl

/-- The inverse terminal component is exactly the specified inverse. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/ArrowSquareMapIso.lean:52"
  "adaptation" "Original four specified factor isomorphisms and literal total-cone target."]
theorem squareMapIsoMk_inv_right_right :
    (squareMapIsoMk B S T e₀ e₁ e₂ e₃ h₀ h₁ h₂ h₃).inv.right.right = e₃.inv := rfl

end CategoryTheory.Arrow
