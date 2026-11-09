/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.FiberedCategory.GrothendieckSections
public import Colib.Util.References

/-!
# Evaluation equivalence for actual Grothendieck cocartesian sections

The original identity comparison identifies the evaluation of the explicitly constructed pullback
section with the original fiber object. Combined with the proved extension and uniqueness of
vertical components, this gives an equivalence of categories without assuming any presentation.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open CategoryTheory.StrictSections
universe u v u' v'
namespace CategoryTheory.GrothendieckSections
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}) (R : C)

/-- The evaluation comparison is induced by the original pseudofunctor identity isomorphism. -/
def evaluationOriginalIso (x : F.obj ⟨R⟩) :
    (underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) R).obj
        (cocartesianSection F R x) ≅ (GrothendieckFiber.toFiber F R).obj x :=
  (GrothendieckFiber.toFiber F R).mapIso ((Cat.Hom.toNatIso (F.mapId ⟨R⟩)).app x)

instance instEssSurjEvaluation :
    (underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) R).EssSurj where
  mem_essImage y :=
    ⟨cocartesianSection F R (GrothendieckFiber.originalObject F R y),
      ⟨evaluationOriginalIso F R _ ≪≫ eqToIso (GrothendieckFiber.toFiber_originalObject F R y)⟩⟩

instance instIsEquivalenceEvaluation :
    (underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) R).IsEquivalence where

/-- The forward functor is the actual evaluation at the original identity arrow. -/
def evaluationEquivalence :
    underCocartesian (Pseudofunctor.Grothendieck.forget F) R ≌
      Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R :=
  (underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) R).asEquivalence

/-- Actual identity evaluation followed by the concrete original-fiber functor. -/
def originalEvaluation :
    underCocartesian (Pseudofunctor.Grothendieck.forget F) R ⥤ F.obj ⟨R⟩ :=
  underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) R ⋙
    GrothendieckFiber.fromFiber F R

/-- The object is the original evaluated fiber, with only its actual base equality transported. -/
theorem originalEvaluation_obj
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :
    (originalEvaluation F R).obj s = GrothendieckFiber.originalObject F R
      ((underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) R).obj s) := rfl

instance instIsEquivalenceOriginalEvaluation : (originalEvaluation F R).IsEquivalence :=
  inferInstanceAs (_ ⋙ _).IsEquivalence

/-- Evaluation into the original pseudofunctor category is a proved equivalence. -/
@[colib_tag "COL-0353",
  colib_ref "quillen"
    "Quillen/Aglib/CategoryTheory/FiberedCategory/GrothendieckSectionEquivalence.lean:26-70"
    "adaptation"
    "Identity evaluation of Grothendieck cocartesian sections is an equivalence"]
def originalEvaluationEquivalence :
    underCocartesian (Pseudofunctor.Grothendieck.forget F) R ≌ F.obj ⟨R⟩ :=
  (originalEvaluation F R).asEquivalence

/-- Evaluation of the canonical pullback section uses the original identity comparison. -/
def originalEvaluationSectionIso (x : F.obj ⟨R⟩) :
    (originalEvaluation F R).obj (cocartesianSection F R x) ≅ x :=
  (GrothendieckFiber.fromFiber F R).mapIso (evaluationOriginalIso F R x)

end CategoryTheory.GrothendieckSections
