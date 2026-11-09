/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPseudofunctor
public import Colib.CategoryTheory.FiberedCategory.CocartesianSectionTransition

/-!
# Actual affine bounded-above-flat cocartesian sections

Adapted from the corresponding bounded-flat section constructions in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native geometric objects and structures.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.StrictSections CategoryTheory.GrothendieckSections
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual Grothendieck total category of bounded-flat affine pullback. -/
abbrev BoundedAboveFlatAffineTotal :=
  Pseudofunctor.Grothendieck boundedAboveFlatAffinePseudofunctor.{u}

/-- The original projection to the coefficient ring. -/
def boundedAboveFlatAffineProjection : BoundedAboveFlatAffineTotal.{u} ⥤ CommRingCat.{u} :=
  Pseudofunctor.Grothendieck.forget boundedAboveFlatAffinePseudofunctor

/-- Actual cocartesian sections, with vertical natural transformations as morphisms. -/
abbrev BoundedAboveFlatAffineSections (R : CommRingCat.{u}) :=
  underCocartesian boundedAboveFlatAffineProjection R

/-- Coefficient change is literal restriction of coslice indices. -/
def boundedAboveFlatAffineSectionsMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    BoundedAboveFlatAffineSections R ⥤ BoundedAboveFlatAffineSections S :=
  underCocartesianReindex boundedAboveFlatAffineProjection f

/-- A strict category-valued diagram built from the actual geometric pseudofunctor. -/
def boundedAboveFlatAffineSectionsFunctor : CommRingCat.{u} ⥤ Cat where
  obj R := ↧(BoundedAboveFlatAffineSections R)
  map f := (boundedAboveFlatAffineSectionsMap f).toCatHom
  map_id R := by
    apply Cat.Hom.ext
    exact underCocartesianReindex_id boundedAboveFlatAffineProjection R
  map_comp f g := by
    apply Cat.Hom.ext
    exact underCocartesianReindex_comp boundedAboveFlatAffineProjection f g

/-- Evaluation at the original identity arrow, into the actual original Grothendieck fiber. -/
def boundedAboveFlatAffineSectionsEvaluation (R : CommRingCat.{u}) :
    BoundedAboveFlatAffineSections R ⥤ Functor.Fiber boundedAboveFlatAffineProjection R :=
  underCocartesianEvaluation boundedAboveFlatAffineProjection R

/-- The section of an original complex consists of its actual coefficient pullbacks. -/
def boundedAboveFlatAffinePullbackSection (R : CommRingCat.{u})
    (x : (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory) :
    BoundedAboveFlatAffineSections R :=
  CategoryTheory.GrothendieckSections.cocartesianSection
    boundedAboveFlatAffinePseudofunctor R x

/-- Concrete evaluation into the original bounded-flat category. -/
def boundedAboveFlatAffineOriginalEvaluation (R : CommRingCat.{u}) :
    BoundedAboveFlatAffineSections R ⥤
      (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory :=
  CategoryTheory.GrothendieckSections.originalEvaluation
    boundedAboveFlatAffinePseudofunctor R

instance instIsEquivalenceBoundedAboveFlatAffineOriginalEvaluation (R : CommRingCat.{u}) :
    (boundedAboveFlatAffineOriginalEvaluation R).IsEquivalence :=
  inferInstanceAs (CategoryTheory.GrothendieckSections.originalEvaluation
    boundedAboveFlatAffinePseudofunctor R).IsEquivalence

/-- A proved categorical equivalence retaining the original evaluation functor. -/
@[colib_tag "COL-0355",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
      SectionEquivalence.lean:31-54"
    "adaptation" "Actual affine section evaluation with its native bounded-above-flat target"]
def boundedAboveFlatAffineSectionEquivalence (R : CommRingCat.{u}) :
    BoundedAboveFlatAffineSections R ≌
      (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory :=
  (boundedAboveFlatAffineOriginalEvaluation R).asEquivalence

/-- Every value of the canonical section is the literal original coefficient pullback. -/
theorem boundedAboveFlatAffinePullbackSection_obj {R S : CommRingCat.{u}} (h : R ⟶ S)
    (x : (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory) :
    ((boundedAboveFlatAffinePullbackSection R x).obj.val.obj (Under.mk h)).fiber =
      (boundedAboveFlatPerfectPullback (Spec.map h)).obj x := rfl

/-- Evaluation at an actual coefficient arrow retains the original target fiber. -/
def boundedAboveFlatAffineEvaluationAt (R : CommRingCat.{u}) (j : Under R) :
    BoundedAboveFlatAffineSections R ⥤
      (boundedAboveFlatPerfectComplex (Spec j.right).toRingedSpace).FullSubcategory :=
  originalEvaluationAt boundedAboveFlatAffinePseudofunctor R j

/-- The actual original transition compares geometric pullback with evaluation at the arrow. -/
def boundedAboveFlatAffineEvaluationPullbackIso (R : CommRingCat.{u}) (j : Under R) :
    boundedAboveFlatAffineOriginalEvaluation R ⋙ boundedAboveFlatPerfectPullback (Spec.map j.hom) ≅
      boundedAboveFlatAffineEvaluationAt R j :=
  originalEvaluationTransitionIso boundedAboveFlatAffinePseudofunctor R j

/-- At the identity arrow the evaluation functor is the original identity evaluation. -/
theorem boundedAboveFlatAffineEvaluationAt_id (R : CommRingCat.{u}) :
    boundedAboveFlatAffineEvaluationAt R (Under.mk (𝟙 R)) =
      boundedAboveFlatAffineOriginalEvaluation R := rfl

/-- Naturality retains the actual original geometric pullback on morphisms. -/
theorem boundedAboveFlatAffineEvaluationPullbackIso_naturality (R : CommRingCat.{u})
    {s t : BoundedAboveFlatAffineSections R} (a : s ⟶ t) (j : Under R) :
    (boundedAboveFlatPerfectPullback (Spec.map j.hom)).map
        ((boundedAboveFlatAffineOriginalEvaluation R).map a) ≫
        (boundedAboveFlatAffineEvaluationPullbackIso R j).hom.app t =
      (boundedAboveFlatAffineEvaluationPullbackIso R j).hom.app s ≫
        (boundedAboveFlatAffineEvaluationAt R j).map a :=
  (boundedAboveFlatAffineEvaluationPullbackIso R j).hom.naturality a

/-- Coefficient restriction followed by evaluation is the actual arrow evaluation. -/
theorem boundedAboveFlatAffineSectionsMap_comp_evaluation {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatAffineSectionsMap f ⋙ boundedAboveFlatAffineOriginalEvaluation S =
      boundedAboveFlatAffineEvaluationAt R (Under.mk f) :=
  originalEvaluation_reindex boundedAboveFlatAffinePseudofunctor R f

/-- Evaluation after coefficient restriction retains the full reindexed coefficient arrow. -/
theorem boundedAboveFlatAffineSectionsMap_comp_evaluationAt {R S : CommRingCat.{u}}
    (f : R ⟶ S) (j : Under S) :
    boundedAboveFlatAffineSectionsMap f ⋙ boundedAboveFlatAffineEvaluationAt S j =
      boundedAboveFlatAffineEvaluationAt R ((Under.map f).obj j) :=
  originalEvaluationAt_reindex boundedAboveFlatAffinePseudofunctor R f j

/-- Restriction at the identity ring map is literally the identity functor. -/
theorem boundedAboveFlatAffineSectionsMap_id (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionsMap (𝟙 R) = 𝟭 (BoundedAboveFlatAffineSections R) :=
  underCocartesianReindex_id boundedAboveFlatAffineProjection R

/-- Restriction at a composite ring map is literally the composite restriction. -/
theorem boundedAboveFlatAffineSectionsMap_comp {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatAffineSectionsMap (f ≫ g) =
      boundedAboveFlatAffineSectionsMap f ⋙ boundedAboveFlatAffineSectionsMap g :=
  underCocartesianReindex_comp boundedAboveFlatAffineProjection f g

/-- Canonical section evaluation retains the original pseudofunctor identity comparison. -/
def boundedAboveFlatAffineOriginalEvaluationPullbackSectionIso (R : CommRingCat.{u})
    (x : (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory) :
    (boundedAboveFlatAffineOriginalEvaluation R).obj
      (boundedAboveFlatAffinePullbackSection R x) ≅ x :=
  originalEvaluationSectionIso boundedAboveFlatAffinePseudofunctor R x

end AlgebraicGeometry.Scheme.Modules
