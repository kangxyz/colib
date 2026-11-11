/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.FiberedCategory.CocartesianSectionComposition

/-!
# Invertibility and vertical naturality of cocartesian section transitions

These are the original arrow-transition proofs from `GrothendieckUnderSections.lean` and
`GrothendieckUnderSectionMap.lean`
at Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Only the existing geometric transition is used, with no additional section realization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory
open CategoryTheory.StrictSections
universe u v u' v'
namespace CategoryTheory.GrothendieckSections
variable {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})

/-- The original arrow transition is invertible, by the source section's cocartesianness. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/FiberedCategory/GrothendieckUnderSections.lean:78"
  "adaptation" "Original actual objects, maps and proof on native infrastructure"]
theorem isIso_originalArrowTransition (A : C)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) A)
    {i k : Under A} (f : i ⟶ k) : IsIso (originalArrowTransition F A s f) := by
  have hs : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian f.right
      (sectionArrow F A s f) := s.property f
  exact GrothendieckFiber.isIso_liftedMap F f.right
    (x := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
      (Under.forget A) i).obj s)
    (y := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
      (Under.forget A) k).obj s) (sectionArrow F A s f)

/-- Original fiber transitions are natural in every vertical section map. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/FiberedCategory/GrothendieckUnderSectionMap.lean:23"
  "adaptation" "Original actual objects, maps and proof on native infrastructure"]
theorem originalArrowTransition_naturality (A : C)
    {s t : underCocartesian (Pseudofunctor.Grothendieck.forget F) A} (α : s ⟶ t)
    {i k : Under A} (f : i ⟶ k) :
    (F.map f.right.toLoc).toFunctor.map ((originalEvaluationAt F A i).map α) ≫
        originalArrowTransition F A t f =
      originalArrowTransition F A s f ≫ (originalEvaluationAt F A k).map α := by
  have hs : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian f.right
      (sectionArrow F A s f) := s.property f
  have ht : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian f.right
      (sectionArrow F A t f) := t.property f
  exact GrothendieckFiber.liftedMap_naturality F f.right
    ((cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) (Under.forget A) i).map α)
    ((cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) (Under.forget A) k).map α)
    (sectionArrow F A s f) (sectionArrow F A t f) (α.hom.val.naturality f).symm

end CategoryTheory.GrothendieckSections
