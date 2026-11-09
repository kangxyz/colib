/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.FiberedCategory.CocartesianSections

/-!
# Faithfulness of original cocartesian-section evaluation

A vertical transformation is determined by its identity component because every original section
transition is strongly cocartesian. This does not assume that any section exists over a given
object.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v u' v'
namespace CategoryTheory.StrictSections
variable {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]
  (π : E ⥤ C) (R : C)

/-- The actual arrow from the identity object of a coslice. -/
def initialArrow (j : Under R) : Under.mk (𝟙 R) ⟶ j := Under.homMk j.hom

private theorem component_isHomLift {J : Type*} [Category* J] (q : J ⥤ C)
    {s t : StrictSections π q} (a : s ⟶ t) (j : J) :
    π.IsHomLift (𝟙 (q.obj j)) (a.val.app j) :=
  ((fiberEvaluation π q j).map a).property

/-- Vertical transformations of cocartesian sections are determined at the identity object. -/
instance : (underCocartesianEvaluation π R).Faithful where
  map_injective {s t} a b h := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    apply NatTrans.ext
    funext j
    have hs : π.IsStronglyCocartesian j.hom (s.obj.val.map (initialArrow R j)) :=
      s.property (initialArrow R j)
    have ha : π.IsHomLift (𝟙 j.right) (a.hom.val.app j) :=
      component_isHomLift π (Under.forget R) a.hom j
    have hb : π.IsHomLift (𝟙 j.right) (b.hom.val.app j) :=
      component_isHomLift π (Under.forget R) b.hom j
    apply Functor.IsStronglyCocartesian.ext π j.hom
      (s.obj.val.map (initialArrow R j)) (𝟙 j.right)
    rw [a.hom.val.naturality, b.hom.val.naturality]
    have h0 : a.hom.val.app (Under.mk (𝟙 R)) = b.hom.val.app (Under.mk (𝟙 R)) :=
      congrArg Subtype.val h
    rw [h0]

end CategoryTheory.StrictSections
