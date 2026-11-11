/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Equality of Grothendieck-valued functors with zero fibers

Equality of the original objects and of the base functors determines all arrows when the
specified target fibers are zero. The proof uses the stored base-functor equality rather
than computing any particular total-category arrow.
-/
/-! Adapted from
`Quillen/Aglib/CategoryTheory/FiberedCategory/GrothendieckZeroExt.lean`
at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Pseudofunctor.Grothendieck

variable {C : Type u₁} [Category.{v₁} C] {B : Type u₂} [Category.{v₂} B]
  {P : Pseudofunctor (LocallyDiscrete B) Cat.{v₃, u₃}}

/-- Equal original objects and equal base functors determine a functor whose fibers are zero. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/FiberedCategory/GrothendieckZeroExt.lean:29"
  "adaptation" "Original actual objects, maps and proof on native infrastructure"]
theorem functor_ext_of_base_of_zero {S T : C ⥤ Pseudofunctor.Grothendieck P}
    (ho : ∀ X, S.obj X = T.obj X)
    (hb : S ⋙ forget P = T ⋙ forget P)
    (hz : ∀ X, Limits.IsZero (T.obj X).fiber) : S = T := by
  refine CategoryTheory.Functor.ext ho ?_
  intro X Y f
  have he {x y : Pseudofunctor.Grothendieck P} (h : x = y) :
      (eqToHom h).base = eqToHom (congrArg base h) := eqToHom_map (forget P) h
  refine Hom.ext _ _ ?_ ?_
  · simp only [categoryStruct_comp_base, he]
    exact CategoryTheory.Functor.congr_hom hb f
  · have hY : Limits.IsZero (S.obj Y).fiber := by
      rw [ho Y]
      exact hz Y
    exact hY.eq_of_tgt _ _

end CategoryTheory.Pseudofunctor.Grothendieck
