/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.FiberedCategory.GrothendieckFiberMap
public import Colib.CategoryTheory.FiberedCategory.GrothendieckSectionEquivalence

/-!
# Actual transitions of cocartesian sections

Evaluation at an arbitrary coefficient arrow is compared with the original pseudofunctor applied
to identity evaluation. The comparison is the original section transition's fiber component.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open CategoryTheory.StrictSections
universe u v u' v'
namespace CategoryTheory.GrothendieckSections
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}) (R : C)

/-- Evaluation at an actual coefficient arrow, retaining its original fiber object. -/
def originalEvaluationAt (j : Under R) :
    underCocartesian (Pseudofunctor.Grothendieck.forget F) R ⥤ F.obj ⟨j.right⟩ :=
  cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) (Under.forget R) j ⋙
    GrothendieckFiber.fromFiber F j.right

/-- The identity transition with its actual evaluated-fiber endpoints explicit. -/
abbrev transitionArrow
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) (j : Under R) :
    ((underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) R).obj s).val ⟶
      ((cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
        (Under.forget R) j).obj s).val := s.obj.val.map (initialArrow R j)

/-- The actual fiber component of the section transition from the identity to `j`. -/
def originalTransition (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R)
    (j : Under R) :
    (F.map j.hom.toLoc).toFunctor.obj ((originalEvaluation F R).obj s) ⟶
      (originalEvaluationAt F R j).obj s := by
  have hs : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian j.hom
      (transitionArrow F R s j) := s.property (initialArrow R j)
  exact GrothendieckFiber.liftedMap F j.hom
    (x := (underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) R).obj s)
    (y := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
      (Under.forget R) j).obj s) (transitionArrow F R s j)

instance instIsIsoOriginalTransition
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) (j : Under R) :
    IsIso (originalTransition F R s j) := by
  have hs : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian j.hom
      (transitionArrow F R s j) := s.property (initialArrow R j)
  exact GrothendieckFiber.isIso_liftedMap F j.hom
    (x := (underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) R).obj s)
    (y := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
      (Under.forget R) j).obj s) (transitionArrow F R s j)

/-- The original transition is invertible by actual strong cocartesianness. -/
def originalTransitionIso
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) (j : Under R) :
    (F.map j.hom.toLoc).toFunctor.obj ((originalEvaluation F R).obj s) ≅
      (originalEvaluationAt F R j).obj s := asIso (originalTransition F R s j)

/-- The original transition is natural in actual vertical section morphisms. -/
theorem originalTransition_naturality
    {s t : underCocartesian (Pseudofunctor.Grothendieck.forget F) R}
    (a : s ⟶ t) (j : Under R) :
    (F.map j.hom.toLoc).toFunctor.map ((originalEvaluation F R).map a) ≫
        originalTransition F R t j =
      originalTransition F R s j ≫ (originalEvaluationAt F R j).map a := by
  have hs : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian j.hom
      (transitionArrow F R s j) := s.property (initialArrow R j)
  have ht : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian j.hom
      (transitionArrow F R t j) := t.property (initialArrow R j)
  exact GrothendieckFiber.liftedMap_naturality F j.hom
    ((underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) R).map a)
    ((cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) (Under.forget R) j).map a)
    (transitionArrow F R s j) (transitionArrow F R t j)
    (a.hom.val.naturality (initialArrow R j)).symm

/-- The actual section transitions form a natural isomorphism of original evaluation functors. -/
def originalEvaluationTransitionIso (j : Under R) :
    originalEvaluation F R ⋙ (F.map j.hom.toLoc).toFunctor ≅ originalEvaluationAt F R j :=
  NatIso.ofComponents (fun s => originalTransitionIso F R s j)
    (fun a => originalTransition_naturality F R a j)

/-- Reindexing followed by evaluation is the original evaluation at the reindexed arrow. -/
theorem originalEvaluationAt_reindex {S : C} (f : R ⟶ S) (j : Under S) :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
        originalEvaluationAt F S j =
      originalEvaluationAt F R ((Under.map f).obj j) := rfl

/-- Reindexing followed by identity evaluation is evaluation at the actual coefficient arrow. -/
theorem originalEvaluation_reindex {S : C} (f : R ⟶ S) :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
        originalEvaluation F S = originalEvaluationAt F R (Under.mk f) := by
  change originalEvaluationAt F R (Under.mk (f ≫ 𝟙 S)) = _
  let H : (R ⟶ S) →
      (underCocartesian (Pseudofunctor.Grothendieck.forget F) R ⥤ F.obj ⟨S⟩) :=
    fun h => originalEvaluationAt F R (Under.mk h)
  exact congrArg H (Category.comp_id f)


end CategoryTheory.GrothendieckSections
