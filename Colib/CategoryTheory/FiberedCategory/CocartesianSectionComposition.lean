/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.FiberedCategory.CocartesianSectionTransition
public import Colib.CategoryTheory.FiberedCategory.GrothendieckFiberComposition

/-!
# Composition of original section transitions

Every actual coslice arrow supplies the original fiber transition. The actual section functor
laws retain the original pseudofunctor composition and identity components.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open CategoryTheory.StrictSections
universe u v u' v'
namespace CategoryTheory.GrothendieckSections
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}) (R : C)

/-- The original evaluation isomorphism retains the literal extracted transition component. -/
theorem originalEvaluationTransitionIso_hom_app
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) (j : Under R) :
    (originalEvaluationTransitionIso F R j).hom.app s = originalTransition F R s j := rfl

/-- The section arrow with both evaluated-fiber endpoints explicit. -/
abbrev sectionArrow
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R)
    {j k : Under R} (a : j ⟶ k) :
    ((cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
      (Under.forget R) j).obj s).val ⟶
    ((cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
      (Under.forget R) k).obj s).val := s.obj.val.map a

/-- The original transition at any actual coefficient arrow in the coslice. -/
def originalArrowTransition
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R)
    {j k : Under R} (a : j ⟶ k) :
    (F.map a.right.toLoc).toFunctor.obj ((originalEvaluationAt F R j).obj s) ⟶
      (originalEvaluationAt F R k).obj s := by
  have hs : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian a.right
      (sectionArrow F R s a) := s.property a
  exact GrothendieckFiber.liftedMap F a.right
    (x := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
      (Under.forget R) j).obj s)
    (y := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
      (Under.forget R) k).obj s) (sectionArrow F R s a)

/-- At the initial arrow this is the unchanged original evaluation transition. -/
theorem originalArrowTransition_initial
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) (j : Under R) :
    originalArrowTransition F R s (initialArrow R j) = originalTransition F R s j := rfl

/-- Strict coefficient restriction retains every original transition at the reindexed arrow. -/
theorem originalArrowTransition_reindex {S : C} (f : R ⟶ S)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R)
    {j k : Under S} (a : j ⟶ k) :
    originalArrowTransition F S
        ((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f).obj s) a =
      originalArrowTransition F R s ((Under.map f).map a) := rfl

/-- Original section composition retains the actual pseudofunctor composition component. -/
@[colib_tag "COL-0356",
  colib_ref "quillen"
    "Quillen/Aglib/CategoryTheory/FiberedCategory/CocartesianSectionComposition.lean"
    "adaptation" "Actual Grothendieck section transition and coefficient coherence"]
theorem originalArrowTransition_comp
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R)
    {j k l : Under R} (a : j ⟶ k) (b : k ⟶ l) :
    originalArrowTransition F R s (a ≫ b) =
      (F.mapComp a.right.toLoc b.right.toLoc).hom.toNatTrans.app
          ((originalEvaluationAt F R j).obj s) ≫
        (F.map b.right.toLoc).toFunctor.map (originalArrowTransition F R s a) ≫
          originalArrowTransition F R s b := by
  have ha : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian a.right
      (sectionArrow F R s a) := s.property a
  have hb : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian b.right
      (sectionArrow F R s b) := s.property b
  have hab : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian
      (a.right ≫ b.right) (sectionArrow F R s (a ≫ b)) := s.property (a ≫ b)
  let x := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
    (Under.forget R) j).obj s
  let y := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
    (Under.forget R) k).obj s
  let z := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
    (Under.forget R) l).obj s
  exact (GrothendieckFiber.liftedMap_congr F (a.right ≫ b.right) (x := x) (y := z)
    (sectionArrow F R s (a ≫ b)) (sectionArrow F R s a ≫ sectionArrow F R s b)
    (s.obj.val.map_comp a b)).trans
      (GrothendieckFiber.liftedMap_comp F a.right b.right (x := x) (y := y) (z := z)
        (sectionArrow F R s a) (sectionArrow F R s b))

/-- The original identity-to-composite transition is the genuine two-arrow coefficient route. -/
theorem originalTransition_comp {S T : C} (f : R ⟶ S) (g : S ⟶ T)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :
    originalTransition F R s (Under.mk (f ≫ g)) =
      (F.mapComp f.toLoc g.toLoc).hom.toNatTrans.app ((originalEvaluation F R).obj s) ≫
        (F.map g.toLoc).toFunctor.map (originalTransition F R s (Under.mk f)) ≫
          originalArrowTransition F R s
            (Under.homMk g : Under.mk f ⟶ Under.mk (f ≫ g)) := by
  exact originalArrowTransition_comp F R s (initialArrow R (Under.mk f))
    (Under.homMk g : Under.mk f ⟶ Under.mk (f ≫ g))

/-- Original section identities retain the actual pseudofunctor unit component. -/
theorem originalArrowTransition_id
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) (j : Under R) :
    originalArrowTransition F R s (𝟙 j) =
      (F.mapId ⟨j.right⟩).hom.toNatTrans.app ((originalEvaluationAt F R j).obj s) := by
  let x := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
    (Under.forget R) j).obj s
  have : (Pseudofunctor.Grothendieck.forget F).IsHomLift (𝟙 j.right) (𝟙 x.val) :=
    IsHomLift.id x.property
  have hj : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian (𝟙 j.right)
      (sectionArrow F R s (𝟙 j)) := s.property (𝟙 j)
  exact (GrothendieckFiber.liftedMap_congr F (𝟙 j.right) (x := x) (y := x)
    (sectionArrow F R s (𝟙 j)) (𝟙 x.val) (s.obj.val.map_id j)).trans
      (GrothendieckFiber.liftedMap_id F x)

end CategoryTheory.GrothendieckSections
