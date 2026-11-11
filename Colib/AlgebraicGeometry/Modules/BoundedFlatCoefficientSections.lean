/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.CoefficientBaseChange
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPseudofunctor
public import Colib.CategoryTheory.FiberedCategory.CocartesianSections
public import Colib.CategoryTheory.FiberedCategory.GrothendieckSectionEquivalence
public import Colib.CategoryTheory.FiberedCategory.CocartesianSectionTransition

/-!
# Actual bounded-flat sections over joint scheme and coefficient indices

The original geometric pseudofunctor gives actual cocartesian sections, literal coefficient
reindexing, original identity-evaluation equivalences and their genuine transition
isomorphisms.
-/
/-! Adapted from
`Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/CoefficientSections.lean`
at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.StrictSections
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original bounded-flat pullback pseudofunctor on the actual joint native family. -/
def boundedAboveFlatCoefficientPseudofunctor (R : CommRingCat.{u}) :
    Pseudofunctor (LocallyDiscrete (Index R)) Cat :=
  (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).toPseudofunctor.comp
    boundedAboveFlatPerfectPseudofunctor

/-- The actual total category retains every original geometric fiber and transition. -/
abbrev BoundedAboveFlatCoefficientTotal (R : CommRingCat.{u}) :=
  Pseudofunctor.Grothendieck (boundedAboveFlatCoefficientPseudofunctor R)

/-- The original joint scheme and coefficient projection. -/
def boundedAboveFlatCoefficientProjection (R : CommRingCat.{u}) :
    BoundedAboveFlatCoefficientTotal R ⥤ Index R :=
  Pseudofunctor.Grothendieck.forget (boundedAboveFlatCoefficientPseudofunctor R)

variable {R : CommRingCat.{u}}

/-- Each original pseudofunctor fiber is the actual bounded-flat perfect category. -/
theorem boundedAboveFlatCoefficientPseudofunctor_obj (i : Index R) :
    (boundedAboveFlatCoefficientPseudofunctor R).obj ⟨i⟩ = Cat.of ((boundedAboveFlatPerfectComplex
      (space i).toRingedSpace).FullSubcategory) := rfl

/-- Both original index coordinates act by the same original geometric pullback functor. -/
theorem boundedAboveFlatCoefficientPseudofunctor_map {i k : Index R} (f : i ⟶ k) :
    ((boundedAboveFlatCoefficientPseudofunctor R).map f.toLoc).toFunctor =
      boundedAboveFlatPerfectPullback
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) := rfl

/-- Actual cocartesian sections over the coslice of one joint index. -/
abbrev BoundedAboveFlatCoefficientSections (i : Index R) :=
  underCocartesian (boundedAboveFlatCoefficientProjection R) i

/-- Original scheme and coefficient change is literal coslice restriction. -/
def boundedAboveFlatCoefficientSectionsMap {i k : Index R} (f : i ⟶ k) :
    BoundedAboveFlatCoefficientSections i ⥤ BoundedAboveFlatCoefficientSections k :=
  underCocartesianReindex (boundedAboveFlatCoefficientProjection R) f

/-- The same original section categories and reindexings form a strict diagram. -/
def boundedAboveFlatCoefficientSectionsFunctor (R : CommRingCat.{u}) : Index R ⥤ Cat where
  obj i := Cat.of (BoundedAboveFlatCoefficientSections i)
  map f := (boundedAboveFlatCoefficientSectionsMap f).toCatHom
  map_id i := by
    apply Cat.Hom.ext
    exact underCocartesianReindex_id (boundedAboveFlatCoefficientProjection R) i
  map_comp f g := by
    apply Cat.Hom.ext
    exact underCocartesianReindex_comp (boundedAboveFlatCoefficientProjection R) f g

/-- Actual identity evaluation into the specified original geometric fiber. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/CoefficientSections.lean:78"
  "adaptation" "Original actual objects, maps and proof on native infrastructure"]
def boundedAboveFlatCoefficientOriginalEvaluation (i : Index R) :
    BoundedAboveFlatCoefficientSections i ⥤ (boundedAboveFlatPerfectComplex
      (space i).toRingedSpace).FullSubcategory :=
  CategoryTheory.GrothendieckSections.originalEvaluation
    (boundedAboveFlatCoefficientPseudofunctor R) i

instance boundedAboveFlatCoefficientOriginalEvaluation_isEquivalence (i : Index R) :
    (boundedAboveFlatCoefficientOriginalEvaluation i).IsEquivalence :=
  inferInstanceAs (CategoryTheory.GrothendieckSections.originalEvaluation
    (boundedAboveFlatCoefficientPseudofunctor R) i).IsEquivalence

/-- Original identity evaluation is the actual forward equivalence. -/
def boundedAboveFlatCoefficientSectionEquivalence (i : Index R) :
    BoundedAboveFlatCoefficientSections i ≌ (boundedAboveFlatPerfectComplex
      (space i).toRingedSpace).FullSubcategory :=
  (boundedAboveFlatCoefficientOriginalEvaluation i).asEquivalence

/-- The actual cocartesian transition compares evaluation with the original joint pullback. -/
def boundedAboveFlatCoefficientSectionReindexIso {i k : Index R} (f : i ⟶ k) :
    boundedAboveFlatCoefficientSectionsMap f ⋙ boundedAboveFlatCoefficientOriginalEvaluation k ≅
      boundedAboveFlatCoefficientOriginalEvaluation i ⋙
        boundedAboveFlatPerfectPullback
          (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) := by
  unfold boundedAboveFlatCoefficientOriginalEvaluation
  exact eqToIso (CategoryTheory.GrothendieckSections.originalEvaluation_reindex
    (boundedAboveFlatCoefficientPseudofunctor R) i f) ≪≫
    (CategoryTheory.GrothendieckSections.originalEvaluationTransitionIso
      (boundedAboveFlatCoefficientPseudofunctor R) i (Under.mk f)).symm

end AlgebraicGeometry.Scheme.Modules

end

end
