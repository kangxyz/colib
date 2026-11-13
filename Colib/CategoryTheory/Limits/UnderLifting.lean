/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Under categories and left lifting classes

An unpointed square against an underlying under-category map gains a
point from its top arrow. A lift of the resulting square preserves it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MorphismProperty

universe v u

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C] (S : C)

/-- Underlying maps with a left lifting property form the left lifting
class of the inverse image of the right maps. -/
theorem inverseImage_llp (W : MorphismProperty C) :
    W.llp.inverseImage (Under.forget S) = (W.inverseImage (Under.forget S)).llp := by
  ext A B i
  constructor
  · intro hi X Y p hp
    let : HasLiftingProperty i.right p.right := hi p.right hp
    constructor
    intro a b sq
    let sq' : CommSq a.right i.right p.right b.right := ⟨congrArg Under.Hom.right sq.w⟩
    let l := sq'.lift
    have hl : B.hom ≫ l = X.hom := by
      rw [← Under.w i, Category.assoc, sq'.fac_left, Under.w a]
    refine ⟨⟨{ l := Under.homMk l hl, fac_left := ?_, fac_right := ?_ }⟩⟩
    · exact Under.UnderMorphism.ext sq'.fac_left
    · exact Under.UnderMorphism.ext sq'.fac_right
  · intro hi X Y p hp
    constructor
    intro a b sq
    let X' : Under S := Under.mk (A.hom ≫ a)
    let Y' : Under S := Under.mk (A.hom ≫ a ≫ p)
    let p' : X' ⟶ Y' := Under.homMk p (Category.assoc _ _ _)
    let a' : A ⟶ X' := Under.homMk a rfl
    let b' : B ⟶ Y' := Under.homMk b (by
      change B.hom ≫ b = A.hom ≫ a ≫ p
      have h : a ≫ p = i.right ≫ b := sq.w
      rw [h, ← Category.assoc, Under.w i])
    let sq' : CommSq a' i p' b' := ⟨Under.UnderMorphism.ext sq.w⟩
    let : HasLiftingProperty i p' := hi p' hp
    refine ⟨⟨{ l := sq'.lift.right, fac_left := ?_, fac_right := ?_ }⟩⟩
    · exact congrArg Under.Hom.right sq'.fac_left
    · exact congrArg Under.Hom.right sq'.fac_right

end CategoryTheory.Under
