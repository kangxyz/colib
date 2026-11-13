/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.PointedPresheaf
public import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Presentable.Comma
import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.Presentable.Type

/-!
# Presentability of pointed simplicial presheaves

The native small model of the indexing category supplies presentability
ranks. The ranks are transported back along the equivalence of the
ordinary pointed presheaf categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.PointedSimplicialPresheaf

/-- Every pointed simplicial presheaf in the site universe is presentable.
This uses only the underlying category of the site. -/
theorem isPresentable_pointedSimplicialPresheaf {C : Type u} [Category.{v} C]
    (X : PointedSimplicialPresheaf.{max u v} C) : IsPresentable.{max u v} X := by
  let D := AsSmall.{0} C
  let E : (Cᵒᵖ ⥤ SSet.{max u v}) ≌ (Dᵒᵖ ⥤ SSet.{max u v}) :=
    (AsSmall.equiv : C ≌ D).op.congrLeft
  let T := (⊤_ (Cᵒᵖ ⥤ SSet.{max u v}))
  let B := AsSmall.{max u v} SimplexCategory
  let E' : SSet.{max u v} ≌ (Bᵒᵖ ⥤ Type (max u v)) :=
    (AsSmall.equiv : SimplexCategory ≌ B).op.congrLeft
  let e' : (Dᵒᵖ ⥤ SSet.{max u v}) ≌ (Dᵒᵖ ⥤ Bᵒᵖ ⥤ Type (max u v)) := E'.congrRight
  let e : Under T ≌ Under ((E.trans e').functor.obj T) := Under.postEquiv T (E.trans e')
  let : IsLocallyPresentable.{max u v} (Bᵒᵖ ⥤ Type (max u v)) := inferInstance
  let : IsLocallyPresentable.{max u v} (Dᵒᵖ ⥤ Bᵒᵖ ⥤ Type (max u v)) := inferInstance
  let : IsAccessibleCategory.{max u v} (Under ((E.trans e').functor.obj T)) := inferInstance
  have h : IsPresentable.{max u v} (e.functor.obj X) := inferInstance
  obtain ⟨κ, hκ, hX⟩ := h.exists_cardinal
  let : Fact κ.IsRegular := hκ
  exact ⟨κ, hκ, (isCardinalPresentable_iff_of_isEquivalence X κ e.functor).1 hX⟩

end CategoryTheory.PointedSimplicialPresheaf
