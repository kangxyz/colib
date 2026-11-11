/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.FiberedCategory.SectionChangeIndexLaws
public import Colib.CategoryTheory.FiberedCategory.GrothendieckZeroSections
public import Colib.CategoryTheory.FiberedCategory.GrothendieckZeroExt

/-! Strict preservation of one global chosen-zero family by actual change of index. -/
/-! Adapted from
`Quillen/Aglib/CategoryTheory/FiberedCategory/SectionChangeIndexZero.lean`
at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open CategoryTheory.StrictSections CategoryTheory.GrothendieckSections
open CategoryTheory.GrothendieckZeroSections
universe u v w z u' v'
namespace CategoryTheory.SectionChangeIndex
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
    (F : Pseudofunctor (LocallyDiscrete D) Cat.{v', u'}) (K : C ⥤ D)
    (Z : ∀ d : D, F.obj ⟨d⟩) (hZ : ∀ d, IsZero (Z d))
    (hmap : ∀ {d e : D} (f : d ⟶ e), IsZero ((F.map f.toLoc).toFunctor.obj (Z d)))

/-- The target zero is the pullback of the same global family, literally. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/FiberedCategory/SectionChangeIndexZero.lean:28"
  "adaptation" "Original actual objects, maps and proof on native infrastructure"]
theorem restriction_sectionZero (c : C) :
    (underFunctor F K c).obj (sectionZero F Z hZ hmap (K.obj c)) =
      sectionZero (pullback F K) (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
        (fun {_ _} f => hmap (K.map f)) c := by
  apply ObjectProperty.FullSubcategory.ext
  apply Subtype.ext
  apply Pseudofunctor.Grothendieck.functor_ext_of_base_of_zero
  · intro i
    rfl
  · rfl
  · intro i
    exact hZ (K.obj i.right)

end CategoryTheory.SectionChangeIndex
